-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_aps_iff_annihilator_eval_zero
-- name    : ApproxPolySatCH.Main.aps_iff_annihilator_eval_zero
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:36:18.613331+00:00
-- url     : https://prove2.me/theorems/1548dacf-e1e1-4c17-9262-5991fa96def8
-- title:
--   Claim 7 — APS criterion from an annihilator generator
-- statement:
--   Let $\bar H$ be the scalar extension of $H$ to $K=\overline{k}$. If $\bar H$ generates the annihilator of the extended system $\bar f$, then
--   $$0\in\overline{f(K^n)}^{\mathrm{Zar}}\quad\Longleftrightarrow\quad H(0)=0.$$
--   Indeed, every polynomial vanishing on the image is a multiple of $\bar H$. If $H(0)=0$, all such multiples vanish at zero. Conversely, if zero lies in the image closure, $\bar H$ itself must vanish there. Evaluation at zero commutes with $k\hookrightarrow K$, so the condition can be checked over $k$.
-- source:
--   STOC 2027 submission #1125, Claim 7 and proof, pp.17–18; APS/image-closure convention on p.6.

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

theorem ApproxPolySatCH.Main.aps_iff_annihilator_eval_zero {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (H : Poly k (n + 1))
    (hker : annihilator (extendedSystem f) =
      Ideal.span {MvPolynomial.map (algebraMap k (Constants k)) H}) :
    (APS f ↔ MvPolynomial.eval (0 : Fin (n + 1) → k) H = 0) := by sorry
