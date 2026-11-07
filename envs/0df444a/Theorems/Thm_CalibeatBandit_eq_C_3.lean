-- Prove2me | Theorems.Thm_CalibeatBandit_eq_C_3
-- name    : CalibeatBandit.eq_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:23.376191+00:00
-- url     : https://prove2.me/theorems/1ed4521a-9d63-40af-b9d0-a7e44dd42918
-- title:
--   Eq. (C.3) — $\lambda e^{\eta H^{\mathrm{SR}}}+(1-\lambda)e^{\eta H^{\mathrm{Rec}}}\le\sum_jx(j)e^{\eta v(j)}$
-- statement:
--   Let $M^{\mathrm{SR}},M^{\mathrm{Rec}}$ be column-stochastic with columns $m^{\mathrm{SR}}_i$, $m^{\mathrm{Rec}}_i$, let $\lambda\in[0,1]$, $J\in\mathcal A$, $\eta>0$, $v\in\mathbb R^K$, and let $x\in\Delta(\mathcal A)$ solve (3.1): $(I-\lambda M^{\mathrm{SR}})x=(1-\lambda)M^{\mathrm{Rec}}e_J$. With
--   $$H^{\mathrm{SR}}=\frac1\eta\sum_i\log\Bigl(\sum_jm^{\mathrm{SR}}_i(j)e^{\eta x(i)v(j)}\Bigr),\qquad H^{\mathrm{Rec}}=\frac1\eta\log\Bigl(\sum_jm^{\mathrm{Rec}}_J(j)e^{\eta v(j)}\Bigr),$$
--   we have
--   $$\lambda e^{\eta H^{\mathrm{SR}}}+(1-\lambda)e^{\eta H^{\mathrm{Rec}}}\le\sum_j\bigl(\lambda(M^{\mathrm{SR}}x)(j)+(1-\lambda)(M^{\mathrm{Rec}}e_J)(j)\bigr)e^{\eta v(j)}=\sum_jx(j)e^{\eta v(j)} .$$
--
--   This is the step where the fixed point (3.1) lets the mixing learner's potential be controlled by the learner's own mixed strategy.
--
--   Differences from the source:
--   - reading: the printed middle term $(M^{\mathrm{Rec}}_t)(j)$ → $(M^{\mathrm{Rec}}e_J)(j)$; reason: the line above (C.3) derives the bound with $(M^{\mathrm{Rec}}_te_{J_t})(j)$; a matrix evaluated at $j$ is a typo for this vector
--   - generalization: the algorithm's round-$t$ quantities $\lambda_t$, $M^a_t$, $x_t$, $v_t$, $J_t$ → all inputs with the hypotheses the proof uses: column-stochastic matrices, $\lambda\in[0,1]$, $x\in\Delta(\mathcal A)$ solving (3.1), $\eta>0$, any real $v$; reason: the algorithm's quantities are instances
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - encoding: actions $\mathcal A=[K]$ → `Fin K`; reason: a relabelling; same instances
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.2, display (C.3), p.34 (PDF 34); the claim is stated on p.33

import Mathlib
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **(C.3): the mixing step** (§C.2, proof of Lemma C.3, pp.33–34). Let `M^SR`, `M^Rec` be
column-stochastic, `λ ∈ [0, 1]`, `x ∈ Δ(𝒜)` a solution of (3.1)
`(I − λM^SR) x = (1 − λ) M^Rec e_J`, `η > 0` and `v` any real vector, and let
`H^SR = (1/η) ∑_i log(∑_j m^SR_i(j) exp(η x(i) v(j)))`, `H^Rec = (1/η) log(∑_j m^Rec_J(j) exp(η v(j)))`.
Then
`λ exp(ηH^SR) + (1 − λ) exp(ηH^Rec) ≤ ∑_j (λ(M^SR x)(j) + (1 − λ)(M^Rec e_J)(j)) exp(ηv(j))
  = ∑_j x(j) exp(ηv(j))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.3), p.34 (the claim stated on p.33).

**Formalization Note.** The printed middle term has `(M^Rec_t)(j)`; the line above it on p.34
derives the bound with `(M^Rec_t e_{J_t})(j)`, which is what is stated. The paper states the
claim for the algorithm's round-`t` quantities; it is stated here for all inputs satisfying the
hypotheses its proof uses. `m^a_i(j)` is the matrix entry `M j i`. -/
theorem eq_C_3 {K : ℕ} (η lam : ℝ) (hη : 0 < η) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (MSR MRec : Matrix (Fin K) (Fin K) ℝ) (hSR : IsColStochastic MSR)
    (hRec : IsColStochastic MRec) (J : Fin K) (x v : Fin K → ℝ) (hx : IsProbVec x)
    (hfix : (1 - lam • MSR) *ᵥ x = (1 - lam) • (MRec *ᵥ Pi.single J 1)) :
    lam * Real.exp (η * HSRof η MSR x v) + (1 - lam) * Real.exp (η * HRecOf η MRec J v)
        ≤ ∑ j, (lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j)
            * Real.exp (η * v j) ∧
    ∑ j, (lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j) * Real.exp (η * v j)
        = ∑ j, x j * Real.exp (η * v j) := by sorry

end CalibeatBandit
