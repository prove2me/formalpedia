-- Prove2me | Theorems.Thm_FiniteMagmaE677_e677_implies_e255_of_existential_row_transport
-- name    : FiniteMagmaE677.e677_implies_e255_of_existential_row_transport
-- status  : Proved
-- author  : @omegaestable
-- created : 2026-10-14T00:33:41.338879+00:00
-- url     : https://prove2.me/theorems/38268b4e-67eb-4601-a577-b2f0e881b5e3
-- title:
--   Finite E677 implies E255 under existential row transport
-- statement:
--   Let $M$ be an arbitrary finite type, including the empty type, and let $*$ be any total binary operation on $M$. Suppose E677 holds:
--
--   $$y*(x*((y*x)*y))=x\qquad (x,y\in M).$$
--
--   Assume additionally the first-order existential-row transport condition
--
--   $$\forall x\in M\;\exists b\in M\;\forall a\in M\;\exists c\in M:\quad c*(b*(x*((a*x)*a)))=x.$$
--
--   Then E255 holds:
--
--   $$((x*x)*x)*x=x\qquad (x\in M).$$
--
--   This is a conditional sufficient criterion. The witness $b$ is chosen before $a$, while $c$ may depend on both. No associativity, commutativity, or identity element is assumed. The extra transport condition is not asserted to follow from E677; this theorem does not resolve the unrestricted finite implication.
-- source:
--   Original conditional row-transport lemma and proof developed with the contributor, 2026-10-13; E677 and the fixer argument use Equational Theories Project blueprint Chapter 13, Lemma 13.1(i)-(ii), https://teorth.github.io/equational_theories/blueprint/677-chapter.html . The additional transport hypothesis is explicitly stated here and is not attributed to that blueprint.

import Mathlib.Data.Fintype.Card
universe u

theorem FiniteMagmaE677.e677_implies_e255_of_existential_row_transport {α : Type u} [Fintype α]
    (op : α → α → α)
    (h : ∀ x y : α, x = op y (op x (op (op y x) y)))
    (hER : ∀ x : α, ∃ b : α, ∀ a : α, ∃ c : α,
      op c (op b (op x (op (op a x) a))) = x) :
    ∀ x : α, x = op (op (op x x) x) x := by sorry
