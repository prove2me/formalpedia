-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_eq14
-- name    : BregmanPPA.ProxMult.eq14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:40.34728+00:00
-- url     : https://prove2.me/theorems/3440a173-fb95-4e50-b23b-30ad61aa8f24
-- title:
--   (14), proof of Theorem 8, p. 221 — (1/c_k)(∇h_x(x^k) − ∇h_x(x^{k+1})) ∈ ∂ₓl(x^{k+1}, p^{k+1})
-- statement:
--   Assume the hypotheses of Theorem 8: a problem of the form (10); $c_k>0$; $h_x$ a Bregman function on $\mathbb R^n$ with zone $S_x\supseteq C$; $h_p$ a Bregman function on $\mathbb R^m$ with zone $S_p\supseteq\overline{\Omega^+}$ and $\operatorname{im}(\nabla h_p)=\mathbb R^m$; and $\{(x^k,p^k)\}$ conforming to the recursions (12). Then for every $k\ge0$, $p^{k+1}\ge0$ and
--
--   $$\frac1{c_k}\big(\nabla h_x(x^k)-\nabla h_x(x^{k+1})\big)\in\partial_x l(x^{k+1},p^{k+1}).\tag{14}$$
--
--   This is the $x$-component of the identity (13) that makes (12) a Bregman proximal point run on $K$.
--
--   **Formalization Note** The conjunct $p^{k+1}\ge0$ is part of the statement because $l(\cdot,p)$ is identically $-\infty$ on $C$ for $p\not\ge0$, where every vector satisfies the subgradient inequality; with it, (14) is the inclusion for the proper convex function $l(\cdot,p^{k+1})=f+\sum_ip_i^{k+1}g_i+\delta_C$, as in the paper (which uses $p^{k+1}\ge0$ on p. 222). The bounded-away-from-zero hypothesis on $c_k$ is not needed and is omitted.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 221, proof of Theorem 8, display (14)

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

namespace BregmanPPA.ProxMult

/-- (14), proof of Theorem 8, p. 221: along a run of (12), `p^{k+1} ≥ 0` and
`(1/c_k)(∇h_x(x^k) − ∇h_x(x^{k+1})) ∈ ∂ₓ l(x^{k+1}, p^{k+1})`. -/
theorem eq14 {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) (hc : ∀ k, 0 < c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    ∀ k, p (k + 1) ∈ BregmanPPA.IneqMult.nonnegOrthant m ∧
      (c k)⁻¹ • (gradient hx (x k) - gradient hx (x (k + 1)))
        ∈ subdiffX C f g (x (k + 1)) (p (k + 1)) := by sorry

end BregmanPPA.ProxMult
