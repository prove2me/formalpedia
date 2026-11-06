-- Prove2me | Theorems.Thm_FeedbackSwitching_proposition_3
-- name    : FeedbackSwitching.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:17.226283+00:00
-- url     : https://prove2.me/theorems/61d8dfbe-9bf8-4e52-b3fe-f606e562adc7
-- title:
--   Proposition 3 — block guarantee (29)–(31) for one iteration of Algorithm 1
-- statement:
--   Let $K,T\ge2$, $\kappa=2^{-m}$ with an integer $m\ge5$, and $H,\delta,M,\eta$ as in Eq. (28), $\Lambda=\log(eKT)$. Let $w$ be a distribution with $w_i\ge1/(KT)$, prepared by PrepareBlock$(w,\kappa)$ from any optimal solution of the LP (19) for a tournament. For a deterministic loss block of length $1\le h\le H$ with sum $L$, played by one iteration of Algorithm 1, with $\mu=\kappa(1+m/2)$, the output $\hat G$ and the cost $C$ (loss, plus internal switches, plus one) satisfy
--   $$
--   \mathbb E\hat G=C_wL-\xi,\quad\eta\|\hat G\|_\infty\le1,\quad\|\xi\|_\infty\le\frac{2^6\delta h\Lambda}{\kappa},\quad
--   \mathbb EC\le\langle w,L\rangle+1+6\mu h+\delta h^3-\frac{\kappa}{2^{24}Mm\Lambda}\mathbb E\|\hat G\|_w^2 .
--   $$
--   The expected number of switches inside the block, plus one, is at most $1+2\mu h$.
--
--   The negative term is the point: each block pays for the second moment of its own output, as Proposition 2 requires.
--
--   **Formalization Note** $\xi$ is defined by $\mathbb E\hat G=C_wL-\xi$; the bound $\eta\|\hat G\|_\infty\le1$ holds for every coin outcome. Expectations are over i.i.d. uniform coins and are asserted to be of integrable functions.
--
--   Differences from the source:
--   - reading: w prepared by PrepareBlock(w, κ) ("a solution of the LP") → any optimal solution of the LP (19) for the tournament; reason: the paper does not fix which solution; the statement is made for every one
--   - encoding: E Ĝ = C_wL − ξ with ξ unspecified → ξ := C_wL − E Ĝ, with the bound on ‖ξ‖_∞; reason: the first equation of (29) defines ξ; same content
--   - encoding: the block's random draws; E → i.i.d. uniform coins, expectations as integrals asserted integrable; reason: each draw has the law the pseudocode states; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Proposition 3, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_FeedbackSwitching_blockRun
import Definitions.Def_FeedbackSwitching_CSet
import Definitions.Def_FeedbackSwitching_tScore
import Definitions.Def_FeedbackSwitching_prepareBlock
import Definitions.Def_FeedbackSwitching_eq28Params
import Definitions.Def_FeedbackSwitching_preparedInput
open MeasureTheory Matrix

namespace FeedbackSwitching

/-- **Proposition 3 (Block guarantee)**, p.25 (PDF p.27). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

Let `K, T ≥ 2` and `κ = 2^{−m}` with an integer `m ≥ 5`, and set `H, δ, M, η` as in Eq. (28). Let `w`
be a distribution with `w_i ≥ 1/(KT)`, prepared by PrepareBlock`(w, κ)`. Consider a deterministic
loss block of length `1 ≤ h ≤ H` with sum `L`, played by one iteration of Algorithm 1, and put
`µ = κ(1 + m/2)`. Its output `Ĝ` and cost `C` satisfy `EĜ = C_wL − ξ`, `η‖Ĝ‖_∞ ≤ 1` (29),
`‖ξ‖_∞ ≤ 2^6 δhΛ/κ` (30), `EC ≤ ⟨w, L⟩ + 1 + 6µh + δh³ − κ/(2^{24}MmΛ) E‖Ĝ‖²_w` (31). The expected
number of switches inside the block, plus one, is at most `1 + 2µh`.

**Formalization Note.** PrepareBlock uses an arbitrary optimal solution `z` of the LP (19) with
anchor `w` for the selected tournament `A`. One iteration of Algorithm 1 on the block is
`blockRun (preparedInput T m A w z)` on i.i.d. uniform coins, `Ĝ = 1{η‖Z‖_∞ ≤ 1}Z`, and the cost `C`
is the block's loss plus its internal switches plus one (p.24). `ξ` is defined by `EĜ = C_wL − ξ`,
so (29) is the definition of `ξ` plus the pointwise bound. `Λ = log(eKT)`. Expectations are
asserted to be of integrable functions. -/
theorem proposition_3 {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : 2 ≤ T) (m : ℕ) (hm : 5 ≤ m)
    (A : Fin K → Fin K → Prop) (hA : IsTournament A) (w : Fin K → ℝ) (hw : IsProbVec w)
    (hwT : ∀ i, 1 / ((K : ℝ) * T) ≤ w i)
    (z : (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ)) (hz : IsOptimalAssignment A w z)
    (h : ℕ) (hh1 : 1 ≤ h) (hhH : h ≤ eq28H m)
    (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t < h, InUnitCube (ℓ t)) :
    Integrable (fun ω => truncate (eq28Eta K T m)
      (blockZ (preparedInput T m A w z) (fun r _ => ℓ r) h ω)) coinLaw ∧
    (∀ ω i, eq28Eta K T m * |truncate (eq28Eta K T m)
      (blockZ (preparedInput T m A w z) (fun r _ => ℓ r) h ω) i| ≤ 1) ∧
    (∀ i, |(centering w *ᵥ (∑ t ∈ Finset.range h, ℓ t)
        - ∫ ω, truncate (eq28Eta K T m)
            (blockZ (preparedInput T m A w z) (fun r _ => ℓ r) h ω) ∂coinLaw) i|
      ≤ 2 ^ 6 * eq28Delta K T * h * bigLambda K T / baseRate m) ∧
    Integrable (fun ω => ∑ t ∈ Finset.range h,
        ℓ t (blockRun (preparedInput T m A w z) (fun r _ => ℓ r) ω t).X
      + internalSwitches (fun t => (blockRun (preparedInput T m A w z) (fun r _ => ℓ r) ω t).X) h
      + 1) coinLaw ∧
    ∫ ω, (∑ t ∈ Finset.range h,
        ℓ t (blockRun (preparedInput T m A w z) (fun r _ => ℓ r) ω t).X
      + internalSwitches (fun t => (blockRun (preparedInput T m A w z) (fun r _ => ℓ r) ω t).X) h
      + 1) ∂coinLaw
      ≤ w ⬝ᵥ (∑ t ∈ Finset.range h, ℓ t) + 1 + 6 * meanRate m * h + eq28Delta K T * (h : ℝ) ^ 3
        - baseRate m / (2 ^ 24 * eq28M K T * m * bigLambda K T) *
          ∫ ω, wNormSq w (truncate (eq28Eta K T m)
            (blockZ (preparedInput T m A w z) (fun r _ => ℓ r) h ω)) ∂coinLaw ∧
    ∫ ω, internalSwitches (fun t => (blockRun (preparedInput T m A w z) (fun r _ => ℓ r) ω t).X) h
        ∂coinLaw + 1 ≤ 1 + 2 * meanRate m * h := by sorry

end FeedbackSwitching
