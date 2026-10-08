-- Prove2me | Theorems.Thm_FiniteMagmaE677_idempotent_e255
-- name    : FiniteMagmaE677.idempotent_e255
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:17:37.974824+00:00
-- url     : https://prove2.me/theorems/458f9995-9f8e-4cc0-a27e-0ee42b40a93a
-- title:
--   Idempotent elements satisfy equation 255
-- statement:
--   In an arbitrary magma (no E677 hypothesis, no finiteness), every idempotent element satisfies equation 255 at that element: if $x \diamond x = x$, then
--
--   $$x = ((x \diamond x) \diamond x) \diamond x,$$
--
--   since both inner collapses reduce to $x \diamond x = x$. Combined with the orbit-period theorems (periods two and three are impossible in finite E677 magmas), any failure of equation 255 in a finite E677 magma is localized to elements of left-orbit length at least four.
-- source:
--   Elementary observation; recorded as a reusable brick for the Prove2Me mission 'Equational Magmas: E677 → E255 (finite case)'.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.idempotent_e255 {α : Type u}
    (op : α → α → α) (x : α) (hid : op x x = x) :
    x = op (op (op x x) x) x := by sorry
