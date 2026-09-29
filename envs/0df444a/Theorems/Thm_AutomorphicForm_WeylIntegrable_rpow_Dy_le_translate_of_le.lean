-- Prove2me | Theorems.Thm_AutomorphicForm_WeylIntegrable_rpow_Dy_le_translate_of_le
-- name    : AutomorphicForm.WeylIntegrable.rpow_Dy_le_translate_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e8cb1ebd-0bba-58ba-95b5-7bb42dcabbfb
-- title:
--   Translation bound for negative powers of D_y
-- statement:
--   Let $F$ be a number field and let $x,u$ be adeles of $F$, each written as a pair consisting of an infinite part (an element of the infinite adele ring) and a finite part (an element of the finite adele ring of the ring of integers $\mathcal{O}_F$). Let $R$ be a real number and assume that the infinite part of $u$ satisfies $\|u_w\| \le R$ at every infinite place $w$ of $F$, and that the finite part of $u$ lies in `integralFiniteAdeles`, i.e. its component at every $v$ in the height one spectrum of $\mathcal{O}_F$ lies in the valuation ring `v.adicCompletionIntegers`. Let $a \ge 0$ be real. Here $D_y(x) =$ `Dy F x` is the real value of the Haar modulus character `distribHaarChar` of the adele ring at the unit `yUnit (selRel F x.1 x.2)` attached to $x$. The conclusion is the inequality of real powers $$D_y(x)^{-a} \le \bigl((1+R)^{\sum_{w} m_w}\bigr)^{a}\, D_y(x+u)^{-a},$$ the sum being over the infinite places $w$ of $F$ with $m_w$ the multiplicity `w.mult`.
--
--   A bookkeeping estimate showing that the weight function $D_y$, used to measure the size of an adele through the modulus of its associated idele, changes by at most a factor $(1+R)^{\sum_w m_w}$ under translation by an adele with archimedean components bounded by $R$ and integral finite part. It is used in the proof that the difference of a Bruhat–Eisenstein series and its constant term is rapidly decreasing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WeylIntegrable_rpow_Dy_le_translate_of_le.lean

import Definitions.Def_AutomorphicForm_WeylSelectors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.rpow_Dy_le_translate_of_le (F : Type) [Field F] [NumberField F]
    (x u : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) {R : ℝ}
    (hu1 : ∀ w, ‖u.1 w‖ ≤ R)
    (hu2 : u.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (NumberField.RingOfIntegers F) F) {a : ℝ} (ha : 0 ≤ a) :
    Dy F x ^ (-a) ≤ ((1 + R) ^ (∑ w : NumberField.InfinitePlace F, w.mult)) ^ a * Dy F (x + u) ^ (-a) := by sorry
