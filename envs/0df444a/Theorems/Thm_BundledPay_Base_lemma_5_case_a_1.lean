-- Prove2me | Theorems.Thm_BundledPay_Base_lemma_5_case_a_1
-- name    : BundledPay.Base.lemma_5_case_a_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:31.455885+00:00
-- url     : https://prove2.me/theorems/149b11ac-7bae-4b9c-a5cd-79fba772e5ed
-- title:
--   Lemma 5 Case A part 1, p. 34 — corrected interior BP equilibrium
-- statement:
--   Under the base-model assumptions, the coordination and physician-incentive conditions, the interior condition $\Delta c<2w_b(1+I_0)$, and either $\Psi\le\bar\Psi$ or $\Psi<\Psi_0$, a bundled-payment subgame-perfect equilibrium exists. Every such equilibrium has
--
--   $$i_h^\sharp=1,\quad i_p^\sharp=\frac{2(1+I_0)w_b-\Delta c}{4w_b(1-\Psi)},\quad T^\sharp=\frac{-2w_b(1-I_0)+\Delta c+2\Delta r_p}{2}.$$
--
--   The result identifies the gainsharing and effort profile used in the benefit calculation.
--
--   **Formalization Note** The printed condition (34) omits the global comparison with $T=0$ when $\Psi>\bar\Psi$; the additional strict $\Psi_0$ bound supplies it. The condition $\Delta c<2w_b(1+I_0)$ is the interior condition in (34).
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, p. 34, Lemma 5 Case A part 1, eqs. (33)–(34); p. 35, proof

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Lemma 5 Case A part 1, p. 34, corrected for global stage-1 optimality.
The printed condition (34) also needs the integration/savings condition when `Ψ > Ψ̄`. -/
theorem lemma_5_case_a_1 (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (h5 : 2 * P.wb * (1 - P.I0) < P.dc + 2 * P.drp)
    (h6 : P.psi ≤ psiPlus P)
    (h7 : P.psi ≤ psiBar P ∨ P.psi < psi0 P)
    (hint : P.dc < 2 * P.wb * (1 + P.I0))
    (rBP : ℝ) :
    (∃ σ T, IsSPNE P rBP σ T) ∧
      ∀ σ T, IsSPNE P rBP σ T →
        T = Tsharp P ∧ σ T = (1, ipSharp P) := by sorry

end BundledPay.Base
