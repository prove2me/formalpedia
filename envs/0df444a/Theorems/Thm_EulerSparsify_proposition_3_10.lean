-- Prove2me | Theorems.Thm_EulerSparsify_proposition_3_10
-- name    : EulerSparsify.proposition_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:32:25.999863+00:00
-- url     : https://prove2.me/theorems/4a41d8cd-4aa6-423c-89a0-7883756c21cc
-- title:
--   Proposition 3.10 — Gaussian partial colouring in a subspace [RR23; JSSTZ25]
-- statement:
--   Let $c_{\mathrm{tight}}\in(0,\tfrac12)$ and $C\in\mathbb R$. There are $C_{\mathrm{set}}>0$ and $c>0$, depending only on $c_{\mathrm{tight}}$ and $C$, such that the following holds for every $m$. Let $S\subseteq\mathbb R^m$ be a subspace with $\dim(S)\ge2c_{\mathrm{tight}}m$ and let $\mathcal K\subseteq\mathbb R^m$ be symmetric, convex and closed with $\gamma_S(\mathcal K)\ge\exp(-Cm)$. For $g\sim N(0_m,I_m)$ let
--
--   $$x=\arg\min_{x\in C_{\mathrm{set}}\mathcal K\cap[-1,1]^m\cap S}\|x-g\|_2 .$$
--
--   Then, with probability at least $1-\exp(-cm)$,
--
--   $$\bigl|\{i\in[m]:\ |x_i|=1\}\bigr|\ge c_{\mathrm{tight}}\,m .$$
--
--   This is the variant of Rothvoss–Reis' partial colouring from Jambulapati et al. that needs a Gaussian measure bound only on the subspace $S$.
--
--   **Formalization Note** The event is stated for every minimiser of $\|x-g\|_2$ over $C_{\mathrm{set}}\mathcal K\cap[-1,1]^m\cap S$; for closed $\mathcal K$ this set is closed, convex and contains $0$, so the minimiser exists and is unique.
--
--   Differences from the source:
--   - encoding: 𝒦 symmetric and convex → 𝒦 symmetric, convex and closed; reason: the arg min must exist: for m = 1, S = ℝ, 𝒦 = (−a, a) with C_set·a < 1 and |g| ≥ C_set·a no nearest point exists; the only use (Lemma 5.10) has 𝒦 = {x : ‖Σ x_i A_i‖ ≤ 4σ}, which is closed
--   - encoding: "with probability 1 − exp(−Ω(m))" → ∃ c > 0 (depending only on c_tight, C) with probability ≥ 1 − exp(−cm); reason: the meaning of Ω(m)
--   - encoding: x := arg min … → every minimiser of ‖x − g‖₂ over C_set𝒦 ∩ [−1,1]^m ∩ S; reason: for closed 𝒦 the minimiser exists and is unique
--   - encoding: "for a constant C" → every real C; reason: the statement is monotone in C; no sign is printed
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Proposition 3.10 ([RR23; JSSTZ25]), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_EulerSparsify_gaussOn

namespace EulerSparsify

open MeasureTheory ProbabilityTheory Pointwise

/-- **Proposition 3.10** ([RR23; JSSTZ25]; partial colouring in a subspace), p.11, PDF p.13.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Proposition 3.10: "Let c_tight ∈ (0, 1/2) be a constant, let S ⊆ ℝ^m be a subspace with
dim(S) ≥ 2c_tight m, and let 𝒦 ⊆ ℝ^m be symmetric and convex. Suppose γ_S(𝒦) ≥ exp(−Cm) for a
constant C. There is C_set > 0 depending only on c_tight, C such that if g ∼ N(0_m, I_m), and
x := arg min_{x∈C_set𝒦∩[−1,1]^m∩S} ‖x − g‖₂, then |{i ∈ [m] | |x_i| = 1}| ≥ c_tight m with
probability 1 − exp(−Ω(m))."

**Formalization Note.**
* `𝒦` is also assumed closed: otherwise the arg min need not exist (`m = 1`, `S = ℝ`,
  `𝒦 = (−a, a)` with `C_set·a < 1` and `|g| ≥ C_set·a`). For closed `𝒦` the set
  `T = C_set𝒦 ∩ [−1,1]^m ∩ S` is closed, convex and contains `0`, so the minimiser exists and is
  unique; the event is stated for every minimiser of `‖x − g‖₂` over `T`.
* "With probability `1 − exp(−Ω(m))`" is: there is `c > 0`, depending only on `c_tight`, `C`, with
  probability at least `1 − exp(−cm)`. `C_set` and `c` come before `m`, `S`, `𝒦`.
* Symmetric means `−𝒦 = 𝒦`; `γ_S` is `gaussOn`; `g` is standard Gaussian on
  `EuclideanSpace ℝ (Fin m)` and `‖·‖` is its Euclidean norm. -/
theorem proposition_3_10 :
    ∀ c_tight : ℝ, 0 < c_tight → c_tight < 1 / 2 → ∀ C : ℝ,
      ∃ C_set : ℝ, 0 < C_set ∧ ∃ c : ℝ, 0 < c ∧
        ∀ (m : ℕ) (S : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
          (K : Set (EuclideanSpace ℝ (Fin m))),
          2 * c_tight * m ≤ (Module.finrank ℝ S : ℝ) →
          (∀ x ∈ K, -x ∈ K) → Convex ℝ K → IsClosed K →
          ENNReal.ofReal (Real.exp (-(C * m))) ≤ gaussOn S K →
          ENNReal.ofReal (1 - Real.exp (-(c * m))) ≤
            stdGaussian (EuclideanSpace ℝ (Fin m))
              {g | ∀ x ∈ (C_set • K) ∩ {y | ∀ i, |y i| ≤ 1} ∩ (S : Set (EuclideanSpace ℝ (Fin m))),
                (∀ y ∈ (C_set • K) ∩ {y | ∀ i, |y i| ≤ 1} ∩ (S : Set (EuclideanSpace ℝ (Fin m))),
                  ‖x - g‖ ≤ ‖y - g‖) →
                c_tight * m ≤ ((Finset.univ.filter fun i => |x i| = 1).card : ℝ)} := by sorry

end EulerSparsify
