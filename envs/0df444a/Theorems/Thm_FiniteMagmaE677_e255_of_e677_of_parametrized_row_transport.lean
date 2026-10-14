-- Prove2me | Theorems.Thm_FiniteMagmaE677_e255_of_e677_of_parametrized_row_transport
-- name    : FiniteMagmaE677.e255_of_e677_of_parametrized_row_transport
-- status  : Proved
-- author  : @omegaestable
-- created : 2026-10-14T04:15:55.474909+00:00
-- url     : https://prove2.me/theorems/daa82c3e-33eb-4ba3-8e17-84ad0b44e823
-- title:
--   Finite E677 implies E255 under parameterized row transport
-- statement:
--   Let $M$ be a finite type, possibly empty, equipped with an arbitrary total binary operation $*$. Assume E677,
--
--   $$\forall x,y\in M,\quad y*(x*((y*x)*y))=x,$$
--
--   and the parameterized row-transport condition (PRT),
--
--   $$\forall x,a\in M\;\exists c,e\in M:\quad (a*e)*(c*(x*(x*((a*x)*a))))=(x*e)*x.$$
--
--   Then E255 holds:
--
--   $$\forall x\in M,\quad ((x*x)*x)*x=x.$$
--
--   This is a conditional sufficient criterion for the finite E677-to-E255 implication. The witnesses $c$ and $e$ may depend on both $x$ and $a$. The PRT condition is an explicit additional hypothesis; it is not asserted to follow from E677, so this result does not settle the unrestricted implication. No associativity, commutativity, or identity element is assumed.
-- source:
--   Original conditional result T186 in the E677-to-E255 research, with a self-contained proof. The ambient E677 and E255 laws are those of Chapter 13, Lemma 13.1 of the Equational Theories Project blueprint: https://teorth.github.io/equational_theories/blueprint/677-chapter.html. The PRT premise and this conditional implication are original to this contribution, not claims attributed to the blueprint.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.e255_of_e677_of_parametrized_row_transport {α : Type u} [Fintype α]
    (op : α → α → α)
    (h : FiniteMagmaE677.E677 op)
    (hPRT : ∀ x a : α, ∃ c e : α,
      op (op a e) (op c (op x (op x (op (op a x) a)))) = op (op x e) x) :
    FiniteMagmaE677.E255 op := by sorry
