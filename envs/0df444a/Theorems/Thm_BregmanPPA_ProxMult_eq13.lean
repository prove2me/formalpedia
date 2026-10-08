-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_eq13
-- name    : BregmanPPA.ProxMult.eq13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:45.091426+00:00
-- url     : https://prove2.me/theorems/79bb8bcd-089f-4b58-a856-3ca0dd8f18b7
-- title:
--   (13), proof of Theorem 8, pp. 221–222 — (x^{k+1}, p^{k+1}) = (∇h + c_k K)⁻¹(∇h(x^k, p^k))
-- statement:
--   Under the hypotheses of Theorem 8 (with $c_k>0$), let $\{(x^k,p^k)\}$ conform to the recursions (12) and let $h=h_x\oplus h_p$. Then the pair sequence $z^k=(x^k,p^k)$ lies in $S_x\times S_p$ and is a run of the Bregman proximal point algorithm for $K$ on $\mathbb R^{n+m}$:
--
--   $$(x^{k+1},p^{k+1})=(\nabla h+c_kK)^{-1}\big(\nabla h(x^k,p^k)\big),\qquad k\ge0.\tag{13}$$
--
--   With (13), the convergence claims of Theorem 8 follow from Theorem 1 under condition (C1).
--
--   **Formalization Note** (13) is stated in the equivalent form (4): $z^k\in S_x\times S_p$ and $\frac1{c_k}(\nabla h(z^k)-\nabla h(z^{k+1}))\in K(z^{k+1})$, where $\nabla h(x,p)=(\nabla h_x(x),\nabla h_p(p))$ on `WithLp 2 (E n × E m)`.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 221–222, proof of Theorem 8, display (13)

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

namespace BregmanPPA.ProxMult

/-- (13), proof of Theorem 8, pp. 221–222: a run of (12) is a run of the Bregman proximal point
algorithm (3), in its form (4), for `h = h_x ⊕ h_p` and `T = K` on `ℝⁿ⁺ᵐ`:
`(x^{k+1}, p^{k+1}) = (∇h + c_k K)⁻¹(∇h(x^k, p^k))`. -/
theorem eq13 {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) (hc : ∀ k, 0 < c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    BregmanPPA.Convergence.IsBregmanPPARun (prodZone Sx Sp) (sumFn hx hp) (opK C f g) c
      (fun k => pair (x k) (p k)) := by sorry

end BregmanPPA.ProxMult
