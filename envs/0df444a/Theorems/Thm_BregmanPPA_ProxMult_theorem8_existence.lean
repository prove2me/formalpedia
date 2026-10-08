-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_theorem8_existence
-- name    : BregmanPPA.ProxMult.theorem8_existence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:48.189188+00:00
-- url     : https://prove2.me/theorems/e88c2d63-f7a2-407b-9edb-d9de22b24063
-- title:
--   Theorem 8 (existence clause) — if im ∇h_x = ℝⁿ, a sequence conforming to (12) exists from every (x⁰, p⁰) ∈ C × Ω̄⁺
-- statement:
--   Consider a problem of the form (10), a Bregman function $h_x$ on $\mathbb R^n$ with zone $S_x\supseteq C$, and a Bregman function $h_p$ on $\mathbb R^m$ with zone $S_p\supseteq\overline{\Omega^+}$ and $\operatorname{im}(\nabla h_p)=\mathbb R^m$. If also $\operatorname{im}(\nabla h_x)=\mathbb R^n$, then for every sequence of positive scalars $c_k$ bounded away from zero and every $(x^0,p^0)\in C\times\overline{\Omega^+}$ there is an infinite sequence $\{(x^k,p^k)\}$ starting at $(x^0,p^0)$ and conforming to the recursions
--
--   $$x^{k+1}=\arg\min_{x\in C}\Big\{f(x)+\frac1{c_k}h_p^{*+}\big(\nabla h_p(p^k)+c_kg(x)\big)+\frac1{c_k}D_{h_x}(x,x^k)\Big\},\qquad p^{k+1}=\nabla h_p^{*+}\big(\nabla h_p(p^k)+c_kg(x^{k+1})\big).\tag{12}$$
--
--   This is the third sentence of Theorem 8; together with the goal it guarantees that the method never halts.
--
--   **Formalization Note** The page prints "for any $(x^0,p^0))\in C\times\overline{\Omega^+}$" with an extra parenthesis. The step sizes satisfy the positive lower bound assumed at the start of Theorem 8.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 221, Theorem 8 (third sentence)

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

namespace BregmanPPA.ProxMult

/-- Theorem 8, p. 221 (third sentence): if moreover `im ∇h_x = ℝⁿ`, then for every sequence of
positive scalars `c k` bounded away from zero and every `(x⁰, p⁰) ∈ C × Ω̄⁺` an infinite sequence conforming to (12)
and starting at `(x⁰, p⁰)` exists. -/
theorem theorem8_existence {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal)
    (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (himx : gradient hx '' Sx = Set.univ) :
    ∀ c : ℕ → ℝ, (∀ k, 0 < c k) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) → ∀ x₀ ∈ C, ∀ p₀ ∈ BregmanPPA.IneqMult.nonnegOrthant m,
      ∃ (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m), x 0 = x₀ ∧ p 0 = p₀ ∧
        IsProxMultRun C f g Sx hx Sp hp c x p := by sorry

end BregmanPPA.ProxMult
