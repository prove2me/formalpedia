-- Prove2me | Theorems.Thm_BoolCSPDel_lemma_A_3
-- name    : BoolCSPDel.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:25.357282+00:00
-- url     : https://prove2.me/theorems/41720b60-3554-4714-bdc4-54b40438655a
-- title:
--   Lemma A.3 — one decoding call succeeds with probability $1-\delta/K$
-- statement:
--   Take the parameters of §A.1.3, with $\varepsilon,\delta$ powers of two, a frequency vector $f\in\{0,\dots,\mu\}^m$ and $j<K$; put $\ell=\lambda_j$ and $G=B^\top\mathrm{diag}(f)^2B$. Let $H=\ell I+\sum_{r=1}^pa_r^2b_{i_r}b_{i_r}^\top$ be fixed, with $p\le M_{\max}$ and each $a_r\in(0,W_{\max}]$ a multiple of $g_a$, and suppose $\frac12H\preceq G+\ell I\preceq2H$. With probability at least $1-\delta/K$ over the masks and the sketch seeds, Algorithm 3 returns a list $F$ of at most $M_{\max}$ active rows with multipliers $\hat a_i\in(0,W_{\max}]$, each a multiple of $g_a$, and $W=\sum_{i\in F}\hat a_i^2b_ib_i^\top$ satisfies
--
--   $$(1-\varepsilon)(G+\ell I)\preceq W+\ell I\preceq(1+\varepsilon)(G+\ell I).$$
--
--   The masks have any $h$-wise independent Bernoulli($1/4$) law, and the sketch pair is any family with the guarantee of Lemma A.1 at accuracy $\varepsilon_a\sqrt\eta/100$ and failure $\beta_s$.
--
--   This is the main analytic step behind Theorem 5.5.
--
--   Differences from the source:
--   - generalization: sketch pairs built from CountSketch and AMS as in Algorithm 2 → any finite-seed sketch pair with entries in {-1, 0, 1} and the guarantee of Lemma A.1; reason: the paper uses the pairs only through this guarantee (p.54); its pairs are an instance
--   - generalization: masks of the standard polynomial construction → any h-wise independent Bernoulli(1/4) law; reason: p.48 requires only h-wise independence with mean 1/4
--   - encoding: H "independent of the masks and sketch seeds" → H a fixed parameter of the statement; reason: the probability is over masks and seeds only
--   - encoding: the main inputs ε, δ → ε = 2^{-e}, δ = 2^{-g}; reason: §A.1.3, p.53: "We may first round ε and δ down to powers of two"
--   - reading: Algorithms 4 and 5 "Return failure if any modified sketch entry exceeds Cmax in magnitude" → the check covers every entry of every working sketch (EntriesOK); reason: line 1 of Algorithm 4 rescales every entry, and Claim A.24 bounds all copies, queried or not; the stricter check can only add failures, so the Lean success event lies inside the page's
--   - generalization: Lemma A.1's guarantee for A ∈ ℝ^{m×D} → assumed only for rational A and rational query vectors; reason: every working sketch and every computed v_i is rational, so only these instances are used; a pair with the real guarantee has the rational one
--   - encoding: round_g with "fixed tie breaking" → g · round(x / g), ties rounded up; reason: one fixed tie-breaking rule, as the page allows any
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Lemma A.3, p.55; Algorithms 3–7, pp.49–53; §A.1.3, pp.53–54

import Mathlib
import Definitions.Def_BoolCSPDel_decode
import Definitions.Def_BoolCSPDel_dictOracle

open MeasureTheory

namespace BoolCSPDel

/-- **Lemma A.3 (decoding).** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Lemma A.3, p.55, with Algorithms 3–7 (pp.49–53) and §A.1.3 (pp.53–54).

For the parameters of §A.1.3, `f ∈ {0, …, μ}^m`, `j < K` and `ℓ = λ_j`, let `H = ℓI + Σ_r a_r² b_{i_r}b_{i_r}ᵀ` be
fixed, with `p ≤ M_max`, each `a_r ∈ (0, W_max]` a multiple of `g_a`, and `½H ⪯ G + ℓI ⪯ 2H`. With probability at
least `1 − δ/K` over the masks and sketch seeds, Algorithm 3 returns a list of at most `M_max` active rows with
multipliers `â_i ∈ (0, W_max]`, each a multiple of `g_a`, and `W = Σ â_i² b_ib_iᵀ` satisfies
`(1 − ε)(G + ℓI) ⪯ W + ℓI ⪯ (1 + ε)(G + ℓI)`.

**Formalization Note.** `ε`, `δ` are powers of two, as §A.1.3 rounds them. `H` is a fixed parameter, so it is
independent of the seeds. The masks have any `h`-wise independent Bernoulli(1/4) law; the sketch pair is any
finite-seed family with the guarantee of Lemma A.1 at `α = ε_a√η/100`, `β = β_s`, since the paper specifies the
pair only through that guarantee. The seed law makes all masks and pairs mutually independent (p.48). -/
theorem lemma_A_3 {Ωs : Type} [Fintype Ωs] [MeasurableSpace Ωs] [MeasurableSingletonClass Ωs]
    (P : Params) (hm : 1 ≤ P.m) (hD : 1 ≤ P.D) (hμ : 1 ≤ P.μ) (he : 3 ≤ P.e) (hg : 2 ≤ P.g)
    (s₀ : ℕ) (B : Matrix (Fin P.m) (Fin P.D) ℤ) (hB : SparseRows s₀ P.b₀ B)
    (f : Fin P.m → ℕ) (hf : ∀ i, f i ≤ P.μ) (j : ℕ) (hj : j < P.K)
    (pair : SketchPair P.m Ωs) (ν : PMF Ωs)
    (hpair : pair.Guarantee (D := P.D) ν
      ((P.epsA : ℝ) * Real.sqrt (P.eta : ℝ) / 100) (P.betaS : ℝ))
    (ξ : PMF (Fin P.m → Bool)) (hξ : IsHWiseQuarter ξ P.h)
    (l : List (Fin P.m × ℚ)) (hl : ValidRep P l)
    (hH₁ : LoewnerLE ((1 / 2 : ℝ) • hMatrix B (P.lamJ j : ℝ) l)
      (gramR B (fun i => (f i : ℤ)) + (P.lamJ j : ℝ) • (1 : Matrix _ _ ℝ)))
    (hH₂ : LoewnerLE (gramR B (fun i => (f i : ℤ)) + (P.lamJ j : ℝ) • (1 : Matrix _ _ ℝ))
      ((2 : ℝ) • hMatrix B (P.lamJ j : ℝ) l)) :
    seedLaw P ξ ν {ω | ¬ ∃ F, decode P pair B f (P.lamJ j) (l.map fun e => (e.1, e.2 ^ 2)) ω = some F ∧
        F.length ≤ P.Mmax ∧
        (∀ e ∈ F, 0 < f e.idx ∧ 0 < e.mult ∧ e.mult ≤ P.Wmax ∧ ∃ n : ℤ, e.mult = n * P.ga) ∧
        LoewnerLE ((1 - (P.eps : ℝ)) •
            (gramR B (fun i => (f i : ℤ)) + (P.lamJ j : ℝ) • (1 : Matrix _ _ ℝ)))
          (hMatrix B (P.lamJ j : ℝ) (F.map fun e => (e.idx, e.mult))) ∧
        LoewnerLE (hMatrix B (P.lamJ j : ℝ) (F.map fun e => (e.idx, e.mult)))
          ((1 + (P.eps : ℝ)) •
            (gramR B (fun i => (f i : ℤ)) + (P.lamJ j : ℝ) • (1 : Matrix _ _ ℝ)))} ≤
      ENNReal.ofReal ((P.delta : ℝ) / P.K) := by sorry

end BoolCSPDel
