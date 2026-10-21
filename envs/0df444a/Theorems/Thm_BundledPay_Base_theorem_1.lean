-- Prove2me | Theorems.Thm_BundledPay_Base_theorem_1
-- name    : BundledPay.Base.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:40.74718+00:00
-- url     : https://prove2.me/theorems/faca838a-e5d6-45be-a98b-9df600226137
-- title:
--   Theorem 1, p. 15 — corrected all-party benefit under bundling
-- statement:
--   Consider the base model with $\Delta c=c_1-c_2>0$, $\Delta r_p=r_{1,p}-r_{2,p}>0$, $w_b>0$, $I_0\in[0,1]$ and $\Psi\in(0,1)$. If
--
--   $$\Delta c+2\Delta r_p>2w_b(1-I_0),\quad \Psi\le\Psi_+,\quad \Psi<\Psi_0,\quad \Delta c<2w_b(1+I_0),$$
--
--   then, for every fee-for-service Nash equilibrium, there is a bundled payment $r^{BP}<r^{FFS}$ at which a bundled subgame-perfect equilibrium exists and every such equilibrium gives both the hospital and physicians strictly greater payoffs than under fee-for-service. The payer pays strictly less, so all three parties benefit at the same payment.
--
--   **Formalization Note** The last condition is Lemma 5's interior condition (34), missing from printed Theorem 1; it confines the theorem to the regime $0<T<T_{\max}$ of Lemma 5 Case A part 1. For $\Delta c\ge 2w_b(1+I_0)$ (the corner $T=T_{\max}$) the printed conditions (5)–(7) are not sufficient (e.g. $I_0=0$, $w_b=1$, $\Delta r_p=1$, $\Delta c=4$, $\Psi=17/20$: the hospital chooses $T=0$), and the paper gives no corrected condition there, so that regime is not stated. The savings threshold is strict because equality can yield zero payer savings. Equilibria are quantified rather than replaced by the paper's closed-form candidates, and their existence is asserted.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, p. 15, Theorem 1, conditions (5)–(7); p. 35, proof, three benefit comparisons

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Theorem 1, p. 15, corrected by the interior condition in Lemma 5 (34)
and strict payer-savings threshold. Every BP subgame-perfect equilibrium benefits
the hospital and physicians at one common payment below the FFS total. -/
theorem theorem_1 (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (h5 : 2 * P.wb * (1 - P.I0) < P.dc + 2 * P.drp)
    (h6 : P.psi ≤ psiPlus P)
    (h7 : P.psi < psi0 P)
    (hint : P.dc < 2 * P.wb * (1 + P.I0))
    (ihF ipF : ℝ) (hF : IsNashFFS P ihF ipF) :
    ∃ rBP : ℝ, rBP < rFFS P ihF ipF ∧
      (∃ σ T, IsSPNE P rBP σ T) ∧
      ∀ σ T, IsSPNE P rBP σ T →
        hospFFS P ihF ipF < hospBP P rBP T (σ T).1 (σ T).2 ∧
        physFFS P ihF ipF < physBP P T (σ T).1 (σ T).2 := by sorry

end BundledPay.Base
