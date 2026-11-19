-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_binary_oracle_prefix_invariant
-- name    : EdgeSublinearMWIS.Main.binary_oracle_prefix_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:55.431598+00:00
-- url     : https://prove2.me/theorems/39df326f-7092-44c4-a64e-3b120f9fff1e
-- title:
--   Binary-hull oracle: prefix invariant and soundness of rejection
-- statement:
--   Let $V_0\subseteq\{0,1\}^N$ be a finite set. Let a finite deterministic program implement the specified binary-hull oracle transition function. Consider an admissible dialogue: each rational cut contains $\operatorname{conv}(V_0)$ and strictly separates the preceding program query.
--
--   After every prefix of the supplied cuts, the stored state has the complete geometric invariant. In particular, there are a dimension $n\le N$, a current Boolean set $V\subseteq\{0,1\}^n$, and a rational affine map $z\mapsto Az+b$ such that
--   $$
--   A\bigl(\operatorname{conv}(V)\bigr)+b\subseteq\operatorname{conv}(V_0),\qquad
--   V_0\ne\varnothing\Longrightarrow V\ne\varnothing.
--   $$
--   The word state represents this affine map canonically, satisfies its prescribed common integer-height bound, and has the rounded-ellipsoid phase invariant. Rejection is sound:
--   $$
--   \text{the prefix state is rejected}\quad\Longrightarrow\quad
--   \operatorname{conv}(V_0)=\varnothing.
--   $$
--   This invariant includes the zero-dimensional and one-dimensional handlers, exact affine coordinate elimination, and preservation of the model after rejection. It supplies the correctness and state-size interface for the separate execution-bound proof.
-- source:
--   Implementation invariant for Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation: oracleCut, oracleTranscriptState, CoreModel, and CoreGeometry; the induction is admissible_prefix_sound. Supports the exact-feasibility step of Bonnet--Chang, Theorem 2, Section 5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf. Rounded phase geometry follows https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs, EllipsoidSequence.lean and EllipsoidStateSize.lean; exact thin-phase recovery uses the supplied integer lattice reduction implementation.

import Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack

theorem EdgeSublinearMWIS.Main.binary_oracle_prefix_invariant {N : ℕ} (E : Program) (hE : ImplementsBinaryOracle E)
    (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
    (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
    (hadm : AdmissibleDialogue E bound N Orig qs cuts) (i : ℕ) (hi : i ≤ cuts.length) :
    CoreGeometry N Orig (oracleTranscriptState (cuts.take i)).2 ∧
      ((oracleTranscriptState (cuts.take i)).1=true → binaryHull Orig=∅) := by sorry
