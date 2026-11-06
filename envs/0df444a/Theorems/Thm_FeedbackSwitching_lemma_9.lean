-- Prove2me | Theorems.Thm_FeedbackSwitching_lemma_9
-- name    : FeedbackSwitching.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:15.970813+00:00
-- url     : https://prove2.me/theorems/16d28502-9d98-4006-bc99-895b6d14b1e9
-- title:
--   Lemma 9 — $\mathbb EZ=C_wL$ and $\mathbb E\|Z\|_w^2\le(2^{14}mL_0/\kappa)(\Gamma+\mu h/16)$
-- statement:
--   Let $(p,x)$ be a holding family, $\kappa=2^{-m}$ with an integer $m\ge5$, $\kappa\lambda_{\max}\le1/4$, and $h\ge1$ an integer with $h\kappa\le1/8$. Let $w$ be a positive probability vector with $w\le2p$, let $(\Psi_s)_s$ satisfy conditions (ii) and (iii) of Definition 5 with $L_0\ge1$, and suppose the scores form a score rule for each $P_\tau$, $\tau\in[\kappa,1]$. Run the block procedure with these inputs and $M\ge1$. For deterministic $\ell_1,\dots,\ell_h\in[0,1]^K$ with sum $L$, the raw corrected estimate $Z$ of Eq. (27) satisfies, with $\mu=\kappa(1+m/2)$,
--   $$
--   \mathbb EZ=C_wL,\qquad\mathbb E\|Z\|_w^2\le\frac{2^{14}mL_0}{\kappa}\Big(\Gamma(\ell_{1:h})+\frac{\mu h}{16}\Big).
--   $$
--   The steering gain thus pays for the second moment of the block estimate, including its squared mean.
--
--   **Formalization Note** $Z$ is the block procedure's raw estimate on i.i.d. uniform coins; $\mathbb EZ$ is the integral of an integrable vector-valued function.
--
--   Differences from the source:
--   - generalization: a fixed tournament orientation defines the comparisons in the score-rule hypothesis → any relation A; reason: Definition 4(i) is not used for the moments of Z; for the selected tournament the statement is the paper's
--   - encoding: the block procedure's random draws; E → the procedure on i.i.d. uniform coins, expectations as integrals asserted integrable; reason: each draw has the law the pseudocode states; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Lemma 9, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_FeedbackSwitching_blockRun
import Definitions.Def_FeedbackSwitching_tScore
import Definitions.Def_FeedbackSwitching_steeringGain
open MeasureTheory Matrix

namespace FeedbackSwitching

/-- **Lemma 9 (Estimation is paid for by steering)**, p.31 (PDF p.33). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

Let `(p, x)` be a holding family, `κ = 2^{−m}` with an integer `m ≥ 5`, `κλ_max ≤ 1/4`, `h ≥ 1` an
integer with `hκ ≤ 1/8`. Let `w` be a positive probability vector with `w ≤ 2p`, let `(Ψ_s)`
satisfy conditions (ii) and (iii) of Definition 5 with `L₀ ≥ 1`, and suppose the scores form a
score rule for each `P_τ` with `τ ∈ [κ, 1]`. Run the block procedure in lines 5 to 8 of Algorithm 1
with these inputs and `M ≥ 1`, forming the chunk estimates `G_J = ∑_{t∈J} Ψ_{X_t}ℓ_t`. For
deterministic `ℓ_1, …, ℓ_h ∈ [0,1]^K` with sum `L`, the raw corrected estimate `Z` of Eq. (27)
satisfies, with `µ = κ(1 + m/2)`, `EZ = C_w L` and `E‖Z‖²_w ≤ (2^{14} m L₀/κ)(Γ(ℓ_{1:h}) + µh/16)`.

**Formalization Note.** The block procedure is `blockRun B` on i.i.d. uniform coins with
`B.p = p, B.x = x, B.Ψ = (Ψ_s), B.m = m, B.M = M`; `Z = blockZ B ℓ h`. Conditions (ii) and (iii) of
Definition 5 are written out. `EZ` is the Bochner integral of the vector `Z`, asserted integrable. -/
theorem lemma_9 {K : ℕ} [NeZero K] (A : Fin K → Fin K → Prop) (B : BlockInput K)
    (hpx : IsHoldingPair B.p B.x) (hm : 5 ≤ B.m)
    (hlam : ∀ s, baseRate B.m * lam B.p B.x s ≤ 1 / 4)
    (h : ℕ) (hh : 1 ≤ h) (hhκ : (h : ℝ) * baseRate B.m ≤ 1 / 8)
    (w : Fin K → ℝ) (hw : IsPosProbVec w) (hwp : ∀ i, w i ≤ 2 * B.p i)
    (L₀ : ℝ) (hL₀ : 1 ≤ L₀)
    (hΨ1 : ∀ s, B.Ψ s *ᵥ (fun _ => (1 : ℝ)) = 0) (hΨ2 : ∑ s, B.p s • B.Ψ s = centering w)
    (hΨ3 : ∀ f, ∑ s, B.p s / lam B.p B.x s * wNormSq w ((B.Ψ s - centering w) *ᵥ f)
      ≤ L₀ * wVar B.p f)
    (hΨ4 : ∀ f, ∑ s, B.p s * wNormSq w ((B.Ψ s - centering w) *ᵥ f) ≤ L₀ * wVar B.x f)
    (hscore : ∀ τ, baseRate B.m ≤ τ → τ ≤ 1 → IsScoreRule A (holdingP B.p B.x τ) B.p (B.d τ))
    (hM : 1 ≤ B.M)
    (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t < h, InUnitCube (ℓ t)) :
    Integrable (blockZ B (fun r _ => ℓ r) h) coinLaw ∧
    ∫ ω, blockZ B (fun r _ => ℓ r) h ω ∂coinLaw = centering w *ᵥ (∑ t ∈ Finset.range h, ℓ t) ∧
    Integrable (fun ω => wNormSq w (blockZ B (fun r _ => ℓ r) h ω)) coinLaw ∧
    ∫ ω, wNormSq w (blockZ B (fun r _ => ℓ r) h ω) ∂coinLaw
      ≤ 2 ^ 14 * B.m * L₀ / baseRate B.m *
        (steeringGain B.p B.x B.m ℓ h + meanRate B.m * h / 16) := by sorry

end FeedbackSwitching
