-- Prove2me | Theorems.Thm_FiniteMagmaE677_finite_counterexample
-- name    : FiniteMagmaE677.finite_counterexample
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-10T21:27:33.371245+00:00
-- url     : https://prove2.me/theorems/1c944d9a-70af-4af5-b3d0-1b015fe84dcf
-- title:
--   A finite magma satisfying E677 but violating E255
-- statement:
--   Open alternative resolution target. There exist a natural number $n$, a total binary operation $\diamond$ on $\mathrm{Fin}(n)$, and an element $x\in\mathrm{Fin}(n)$ such that every $p,q\in\mathrm{Fin}(n)$ satisfies
--   $$p=q\diamond(p\diamond((q\diamond p)\diamond q)),$$
--   but
--   $$x\ne((x\diamond x)\diamond x)\diamond x.$$
--   There is no upper bound on $n$ and no associativity, identity, commutativity, or cancellation assumption. The exhibited element excludes the empty carrier. Proving this target supplies a finite counterexample to the main implication. It is an alternative resolution, not an additional prerequisite for proving the implication. No witness is currently supplied.
-- source:
--   Counterexample direction of the finite E677/E255 problem; Equational Theories Project blueprint, Chapter 13, equations (1) and (2): https://teorth.github.io/equational_theories/blueprint/677-chapter.html

import Definitions.Def_FiniteMagmaE677

theorem FiniteMagmaE677.finite_counterexample :
    ∃ n : ℕ, ∃ op : Fin n → Fin n → Fin n,
      FiniteMagmaE677.E677 op ∧
        ∃ x : Fin n, x ≠ op (op (op x x) x) x := by sorry
