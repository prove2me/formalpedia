-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_lemma3
-- name    : BregmanPPA.ProxMult.lemma3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:17.525032+00:00
-- url     : https://prove2.me/theorems/82e5c4ca-5e3c-41b3-84e6-1a50d598e89d
-- title:
--   Lemma 3 — h*⁺ is closed proper convex, finite everywhere and differentiable
-- statement:
--   Let $h$ be a Bregman function on $\mathbb R^m$ with zone $S\supseteq\Omega^+$ and $\operatorname{im}(\nabla h)\supseteq\Omega^+$. Then the monotone conjugate
--
--   $$h^{*+}(z)=\sup_{p\ge0}\{\langle p,z\rangle-h(p)\}$$
--
--   is a closed (lower semicontinuous) proper convex function, finite at every $z\in\mathbb R^m$, and differentiable on all of $\mathbb R^m$.
--
--   In Theorem 8 this is applied to $h_p$ (zone $S_p\supseteq\overline{\Omega^+}\supseteq\Omega^+$, $\operatorname{im}\nabla h_p=\mathbb R^m$): it is what makes the value $h_p^{*+}(\cdot)$ in the $x$-step of (12) a real number and $\nabla h_p^{*+}$ in the $p$-step well defined.
--
--   **Formalization Note** $h^{*+}$ is `EReal`-valued, so finiteness is the claim $-\infty<h^{*+}(z)<+\infty$ for all $z$; convexity is convexity of the epigraph (`IsConvexFn`) and properness is `IsProperFn`. Differentiability is stated for the real-valued function $z\mapsto h^{*+}(z)$ (`toReal`), which is exact because of the finiteness clause.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 216, Lemma 3

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology InertialFB.IFB

namespace BregmanPPA.ProxMult

/-- Lemma 3, p. 216: if `h` is a Bregman function with zone `S ⊇ Ω⁺` and `im ∇h ⊇ Ω⁺`, then
`h*⁺` is a closed proper convex function, finite everywhere and differentiable. -/
theorem lemma3 {m : ℕ} (S : Set (BregmanPPA.IneqMult.E m)) (h : BregmanPPA.IneqMult.E m → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hS : BregmanPPA.IneqMult.posOrthant m ⊆ S)
    (him : BregmanPPA.IneqMult.posOrthant m ⊆ gradient h '' S) :
    LowerSemicontinuous (BregmanPPA.IneqMult.monoConj h) ∧
    IsProperFn (BregmanPPA.IneqMult.monoConj h) ∧
    IsConvexFn (BregmanPPA.IneqMult.monoConj h) ∧
    (∀ z : BregmanPPA.IneqMult.E m, BregmanPPA.IneqMult.monoConj h z ≠ ⊤ ∧ BregmanPPA.IneqMult.monoConj h z ≠ ⊥) ∧
    Differentiable ℝ (fun z : BregmanPPA.IneqMult.E m => (BregmanPPA.IneqMult.monoConj h z).toReal) := by sorry

end BregmanPPA.ProxMult
