-- Prove2me | Theorems.Thm_CritWinSpin_p6b_6_3_rejection_tm
-- name    : CritWinSpin.p6b_6_3_rejection_tm
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:29.684908+00:00
-- url     : https://prove2.me/theorems/37c4337b-c3e1-45c2-aa3a-f6c1a30a1f02
-- title:
--   Quantized uniform rejection composed with an exact PPT cloud proposal
-- statement:
--   Let a PPT proposal machine have exact per-configuration law $\tilde\nu$, where $\tilde\nu$ is a probability distribution supported inside $\nu_y$. There is a PPT postprocessing machine which draws an independent uniform threshold and accepts according to a quantized function $\tilde a_y$.
--
--   The resulting slot output is a probability distribution on $A^N\cup\{\bot\}$, and for every configuration $\sigma$ its acceptance-output probability factors **exactly** as
--   $$
--   \Pr[\mathrm{output}=\sigma]=\tilde\nu(\sigma)\,\tilde a_y(\sigma).
--   $$
--   Moreover $0\le\tilde a_y\le1$, every positive-probability output has positive probability under the ideal rejection kernel, and on the support of $\tilde\nu$,
--   $$
--   \left|\tilde a_y(\sigma)-a_y(\sigma)\right|
--    \le \frac12e^{-2n^2},
--   \qquad
--    a_y(\sigma)=e^{D_y(\sigma)-1}\mathbf 1_{G_y}(\sigma).
--   $$
--   Thus the construction supplies precisely the rejection half of the approximation in steps 1–2 on p.24, while preserving support and exact factorization.
--
--   **Formalization Note.** The statement is independent of the GHS and gadget-parameter hypotheses and is expressed for arbitrary real $\beta$; these properties are needed only for the proposal approximation. It covers all $n$ and $r$, including $r=0$: normalization follows from normalization of $\tilde\nu$ and $0\le\tilde a_y\le1$, with all rejected or undecodable outcomes mapped to $\bot$.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), §6.2, p.22 (definition of $G_y$ and $a_y$) and p.24 (PDF p.25), procedure $\hat L_{T,k}$, step 2: independent uniform-threshold rejection, with exponential weights quantized to polynomially many bits as stipulated in step 1.

import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
set_option autoImplicit false

/-- Step 2 on p.24: compose any exact proposal PPT with quantized uniform-threshold rejection. -/
theorem CritWinSpin.p6b_6_3_rejection_tm (S : SpinLaw) (p Cc : ℕ) (propM : PPT) :
    ∃ slotM : PPT,
      ∀ (n : ℕ) (H : Inst n) (û : ℚ) (y : BinCfg n) (β : ℝ)
        (nuT : Config S (Fin n × Fin (cloudSize p Cc n)) → ℝ),
        (∀ σ, propM.prob (tupleCode [encInst H, encRat û, List.ofFn y])
            (fun s => decCloud S n (cloudSize p Cc n) s = some σ) = nuT σ) →
        (∀ σ, 0 ≤ nuT σ) → ∑ σ, nuT σ = 1 →
        (∀ σ, 0 < nuT σ → 0 < nuProd S β y σ) →
        IsDistribution (slotKernel S p Cc slotM H û y) ∧
        ∃ aT : Config S (Fin n × Fin (cloudSize p Cc n)) → ℝ,
          (∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1) ∧
          (∀ σ, slotKernel S p Cc slotM H û y (some σ) = nuT σ * aT σ) ∧
          (∀ σ, 0 < slotKernel S p Cc slotM H û y (some σ) →
            0 < idealSlot S β (castM H.1) (castV H.2) (û : ℝ) y (some σ)) ∧
          (∀ σ, 0 < nuT σ →
            |aT σ - ay (castM H.1) (castV H.2) (û : ℝ) y σ| ≤
              (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2))) := by sorry
