-- Prove2me | Theorems.Thm_FiniteMagmaE677_e255_of_e677_of_left_parameter_transport
-- name    : FiniteMagmaE677.e255_of_e677_of_left_parameter_transport
-- status  : Proved
-- author  : @omegaestable
-- created : 2026-10-15T00:47:26.205515+00:00
-- url     : https://prove2.me/theorems/a47bcdf3-bb60-4654-a0cb-9ffd426c212f
-- title:
--   Finite E677 implies E255 under left parameter transport
-- statement:
--   Let M be a finite type, possibly empty, equipped with an arbitrary total binary operation *. Assume the E677 law
--
--   $$\forall x,y\in M,\quad x=y*(x*((y*x)*y)),$$
--
--   and the left-parameter transport condition
--
--   $$\forall x,a\in M\;\exists c,e\in M:\quad (e*a)*(c*(x*(x*((a*x)*a))))=(e*x)*x.$$
--
--   Then E255 holds:
--
--   $$\forall x\in M,\quad x=((x*x)*x)*x.$$
--
--   The transport condition is an explicit additional hypothesis and supplies a sufficient criterion for E255; the result does not claim that E677 alone implies it. No associativity, commutativity, or identity element is assumed.
--
--   **Formalization Note** The `Fintype` assumption represents finiteness and includes the empty carrier.
-- source:
--   Original conditional result T190, Left parameter transport, in the E677-to-E255 research corpus. The E677 and E255 formulas follow the Equational Theories Project blueprint, Chapter 13, Lemma 13.1: https://teorth.github.io/equational_theories/blueprint/677-chapter.html. The LPT premise and conditional implication are original to this contribution.

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Theorems.Thm_FiniteMagmaE677_fixer_unique

set_option autoImplicit false

universe u

theorem FiniteMagmaE677.e255_of_e677_of_left_parameter_transport {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op) (hLPT : ∀ x a : α, ∃ c e : α, op (op e a) (op c (op x (op x (op (op a x) a)))) = op (op e x) x) : FiniteMagmaE677.E255 op := by sorry
