-- Prove2me | Theorems.Thm_BC1992_theorem_bellantoni_cook_characterization
-- name    : BC1992.theorem_bellantoni_cook_characterization
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T00:37:22.510211+00:00
-- url     : https://prove2.me/theorems/1279955d-34c6-4c09-ad96-3b8ff8abe0c0
-- title:
--   Main Theorem: The Bellantoni-Cook Recursion-Theoretic Characterization of FP (BC = FP)
-- statement:
--   Establishes the main theorem of Bellantoni and Cook (1992): a unary word function $f : \mathsf{Word} \to \mathsf{Word}$ is definable by a closed program $\mathit{prog} : \mathsf{Fn}\;1\;0$ in the two-sorted Bellantoni-Cook safe recursion algebra if and only if $f$ is computable in polynomial time by a deterministic multi-tape Turing machine ($f \in \mathsf{FP}$):
--
--   $$\forall f : \mathsf{Word} \to \mathsf{Word},\quad \bigl(\exists \mathit{prog} : \mathsf{Fn}\;1\;0,\; \forall x : \mathsf{Word},\; \mathit{prog}.\mathsf{eval}\;[x]\;[] = f(x)\bigr) \iff \mathsf{FP}(f).$$
-- source:
--   Stephen Bellantoni and Stephen Cook, 'A new recursion-theoretic characterization of the polytime functions', Computational Complexity 2 (1992), pp. 97-110 (doi:10.1007/BF01201998). Sections 2-3, Main Theorem, pp. 99-105.

import Definitions.Def_BC1992_Syntax
import Definitions.Def_BC1992_Machines
import Definitions.Def_BC1992_Simulation

namespace BC1992

/-- **Main Theorem (Bellantoni & Cook 1992 — Recursion-Theoretic Characterization of `FP`)**:
    1. (`bc_soundness`) Every BC-definable unary word function belongs to `FP`.
    2. (`bc_completeness`) Every word function in `FP` is BC-definable.
    3. (`defFun_eq_FP`) For every unary word function `f : Word → Word`,
       `(∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x) ↔ FP f`.
    4. (`bcDefinable_iff_FP`) `BCDefinable f ↔ FP f`. -/
theorem theorem_bellantoni_cook_characterization :
    (∀ f : Word → Word, BCDefinable f → FP f) ∧
    (∀ f : Word → Word, FP f → BCDefinable f) ∧
    (∀ f : Word → Word,
      (∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x) ↔ FP f) ∧
    (∀ f : Word → Word, BCDefinable f ↔ FP f) := by
  sorry

end BC1992
