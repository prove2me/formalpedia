-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_value_sandwich
-- name    : FlexCommitRO.BoxExt.value_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:45.972849+00:00
-- url     : https://prove2.me/theorems/9594ca99-7cee-473d-9398-abc7a7214abc
-- title:
--   Proof of Proposition 1, p. 271 — the R-box step, corrected: value(box) ≤ value_R(box) for all R, value(ext) ≤ value(box), value(ext) = inf_R value_R(ext)
-- statement:
--   Let an instance of the RSFC model be given, together with demand bounds $d_t^{\min} \le d_t^{\max}$, $t = 1,\dots,T$. Write $\mathcal U_{\text{box}} = \prod_t [d_t^{\min}, d_t^{\max}]$ and $\mathcal U_{\text{ext}} = \prod_t \{d_t^{\min}, d_t^{\max}\}$, $\operatorname{value}$ for the optimal value of the min-max RSFC problem (5)–(6) and $\operatorname{value}_R$ for the same problem with every decision bounded by $R$ in absolute value. Then:
--
--   1. $\operatorname{value}(\mathcal U_{\text{box}}) \le \operatorname{value}_R(\mathcal U_{\text{box}})$ for every $R \in \mathbb R$;
--   2. $\operatorname{value}(\mathcal U_{\text{ext}}) \le \operatorname{value}(\mathcal U_{\text{box}})$;
--   3. $$\operatorname{value}(\mathcal U_{\text{ext}}) = \inf_{R \in \mathbb R} \operatorname{value}_R(\mathcal U_{\text{ext}}).$$
--
--   Together with the boxed equality, these give $\operatorname{value}(\mathcal U_{\text{box}}) = \operatorname{value}(\mathcal U_{\text{ext}})$.
--
--   **Formalization Note** The page argues that "for an $R$ large enough this restriction does not affect the optimal value". As printed this is false when the optimal value is $-\infty$, which the paper's sign-free data allow (e.g. $T=1$, $\beta_1^+ = -1$, $\beta_1^- = 1$, $\alpha_1^\pm = 0$, $L_1 = U_1 = 0$: then $z_1 = w_0 - w_1$ is unbounded below while every boxed value is finite). The statement is the corrected form, which holds for all data and is what the argument needs.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 271, Appendix, proof of Proposition 1 (continued), "for an R large enough this restriction does not affect the optimal value"

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_Setting

namespace FlexCommitRO.BoxExt

theorem value_sandwich {T : ℕ} (D : RSFCData T) (dmin dmax : Fin T → ℝ)
    (hle : ∀ t, dmin t ≤ dmax t) :
    (∀ R : ℝ, value D (fun t => Set.Icc (dmin t) (dmax t)) ≤
        valueR D (fun t => Set.Icc (dmin t) (dmax t)) R) ∧
      value D (fun t => ({dmin t, dmax t} : Set ℝ)) ≤ value D (fun t => Set.Icc (dmin t) (dmax t)) ∧
      value D (fun t => ({dmin t, dmax t} : Set ℝ)) =
        ⨅ R : ℝ, valueR D (fun t => ({dmin t, dmax t} : Set ℝ)) R := by sorry

end FlexCommitRO.BoxExt
