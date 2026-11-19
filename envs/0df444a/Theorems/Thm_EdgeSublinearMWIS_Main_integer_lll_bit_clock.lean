-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_integer_lll_bit_clock
-- name    : EdgeSublinearMWIS.Main.integer_lll_bit_clock
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:56:17.453466+00:00
-- url     : https://prove2.me/theorems/b4d74ea1-29b1-43e3-8d0c-826999644846
-- title:
--   Integer lattice reduction: polynomial bit clock and output size
-- statement:
--   For every full-rank integer square matrix $B$, the specified deterministic integer lattice-reduction routine has polynomial bit complexity and polynomial output length. More precisely, there are universal natural constants $C>0$ and $q$ such that, writing $L$ for the size of the canonical integer-matrix input,
--   $$
--   \operatorname{time}(B)\le C(L+1)^q,\qquad
--   \operatorname{size}(\operatorname{LLL}(B))\le C(L+1)^q.
--   $$
--   The same constants apply in every dimension. The clock is the charged execution cost of the published typed stack routine; its finite-program realization is provided by the stack simulation interface. This bound supplies the lattice-reduction subroutine used in exact binary-hull feasibility.
-- source:
--   Implementation bound for integerLLLRealizer and integerLLL in Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation; LLL potential, integral Gram determinants, rational bit arithmetic, and coefficient-height estimates. Used in the exact-feasibility step of Bonnet--Chang, Theorem 2, Section 5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf. Lattice reduction follows the integer LLL algorithm of Lenstra--Lenstra--Lovasz (1982), https://doi.org/10.1007/BF01457454.

import Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds EdgeSublinearMWIS.Main.LLLBounds

theorem EdgeSublinearMWIS.Main.integer_lll_bit_clock :
    ∃ C q : ℕ,0 < C ∧ ∀ n (B : Matrix (Fin n) (Fin n) ℤ),
      LinearIndependent ℝ (embed B) →
      integerLLLRealizer.time (integerMatrixInput B) ≤ C*(volume (integerMatrixInput B)+1)^q ∧
      volume (integerLLL (integerMatrixInput B)) ≤ C*(volume (integerMatrixInput B)+1)^q := by sorry
