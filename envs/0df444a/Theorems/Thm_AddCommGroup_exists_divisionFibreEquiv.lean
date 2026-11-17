-- Prove2me | Theorems.Thm_AddCommGroup_exists_divisionFibreEquiv
-- name    : AddCommGroup.exists_divisionFibreEquiv
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:23.567762+00:00
-- url     : https://prove2.me/theorems/e5d51008-2f56-4614-857e-6424e7d4f3fe
-- title:
--   The union of the $71$-division fibres is $G[71]×ℤ/71ℤ$ with a carry law
-- statement:
--   Let $G$ be an additive commutative group and let $Q∈G$. Put $T=\{v∈G:71v=0\}$ and $F=∐_{a∈ℤ/71ℤ}\{X∈G:71X=[a](71Q)\}$. There is an equivalence $e:T×ℤ/71ℤ≃F$ such that $e(v,a)=(a,v+[a]Q)$, its inverse sends $(a,X)$ to $(X-[a]Q,a)$, and $$e(v+w,a+b)_2=e(v,a)_2+e(w,b)_2-⌊([a]+[b])/71⌋(71Q).$$ This identifies the division-fibre extension and its explicit carry correction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem AddCommGroup.exists_divisionFibreEquiv
    (G : Type*) [AddCommGroup G] (Q : G) :
    let T := (nsmulAddMonoidHom (α := G) 71).ker
    let F := Σ a : ZMod 71, {X : G // (71 : ℕ) • X = a.val • ((71 : ℕ) • Q)}
    ∃ e : (T × ZMod 71) ≃ F,
      (∀ (v : T) (a : ZMod 71), (e (v, a)).1 = a ∧
        ((e (v, a)).2 : G) = (v : G) + a.val • Q) ∧
      (∀ x : F, ((e.symm x).1 : G) = (x.2 : G) - x.1.val • Q ∧
        (e.symm x).2 = x.1) ∧
      ∀ (v w : T) (a b : ZMod 71),
        ((e (v + w, a + b)).2 : G) =
          ((e (v, a)).2 : G) + ((e (w, b)).2 : G) -
            ((a.val + b.val) / 71) • ((71 : ℕ) • Q) := by sorry
