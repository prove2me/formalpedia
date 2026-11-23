-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_theorem_4_7
-- name    : BilevelSOC.SecondOrder.Supplement.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:43:37.965315+00:00
-- url     : https://prove2.me/theorems/bcf096e6-6cde-4bba-9b04-6841b7f8582a
-- title:
--   Theorem 4.7 — Clarke regularity and a zero polar cone imply strict local optimality
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions and let $z=(\bar x,\bar y)\in M$ be bilevel feasible. Suppose the extended-real lower value function $\varphi$ is locally finite and locally Lipschitz at $\bar x$, and $-\varphi$ is Clarke regular there. Let $\partial^c\varphi(\bar x)$ denote the Clarke subdifferential and form
--
--   $$Q=\{\nabla F(z)\}\cup\{\nabla G_i(z):i\in\bar I^G\}\cup\{\nabla f(z)-(\xi,0):\xi\in\partial^c\varphi(\bar x)\}\cup\{\nabla g_i(z):i\in\bar I^g\}.$$
--
--   If $Q^\circ=\{0\}$, then $z$ is a strict local minimizer of the bilevel program. This is the Clarke-polar companion criterion; it assumes neither the boundedness nor the LMFCQ hypotheses of Theorem 4.2.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - encoding: locally Lipschitz φ, Clarke regular −φ, and Euclidean Q°={0} → a locally equal real representative, Clarke regularity of its negative, and the zero polar of the full covector union Q42; reason: local representatives determine all the derivative objects, and Euclidean Riesz identification preserves every polar pairing
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 12, Theorem 4.7

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_ValueCriteria
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem theorem_4_7 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (φ : E n → ℝ) (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hrep : ∀ᶠ x in 𝓝 z.1, valueFn D x = (φ x : EReal))
    (hLip : LocallyLipschitzAt φ z.1)
    (hregular : ClarkeRegularAt (fun x => -φ x) z.1)
    (hpolar : dualPolar (Q42 D z φ) = {0}) :
    StrictLocalMin D.F (feasSet D) z := by sorry
end BilevelSOC.SecondOrder.Supplement
