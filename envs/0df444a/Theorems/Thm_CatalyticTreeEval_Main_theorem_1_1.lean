-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_theorem_1_1
-- name    : CatalyticTreeEval.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:45.097421+00:00
-- url     : https://prove2.me/theorems/90ea4086-e8c0-47a8-8031-76018b997054
-- title:
--   Theorem 1.1 — logarithmic free space and subpolynomial catalytic space
-- statement:
--   For every real $\epsilon>0$ there are one finite deterministic machine, positive constants $C_s,C_c,C_t$ and a positive integer $q$, depending only on $\epsilon$, that work for every positive height and label length. Let $I$ be any complete ordered binary TreeEval instance with arbitrary leaf labels and arbitrary full internal truth tables. Let $n$ be the length of its fixed binary encoding and put $L(n)=1+\log_2(n+2)$. The same halting run outputs the complete root label and restores every arbitrary initial catalyst bit, with simultaneous bounds
--
--   $$\mathrm{free}\le\lceil C_sL(n)\rceil,\qquad\mathrm{catalytic}\le\left\lceil2^{C_cL(n)^\epsilon}\right\rceil,\qquad\mathrm{time}\le C_t(n+2)^q.$$
--
--   The guarantee holds for every tape at least as long as the catalytic bound; the machine addresses only its bounded prefix and never reads its endmarker. The constants and the machine precede all sizes, instances and tapes. This is the full Theorem 1.1, with neither a fixed value of $\epsilon$ nor efficient ingredients as hypotheses.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: n-bit TreeEval and O(log n), 2^(O((log n)^ε)), poly(n) bounds → n is the explicit self-delimiting table encoding length; positive shifted logs and upward cell rounding; all longer arbitrary tapes with bounded addressed prefix; reason: the payload has the source input-size order, shifts cover small inputs, and prefix bounds prevent nonuniform tape-length advice
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Theorem 1.1, printed p. 1 (PDF p. 3); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Resources

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Theorem 1.1, printed p.1 / PDF p.3: the complete epsilon-family, simultaneous bounds. -/
theorem theorem_1_1 :
    ∀ ε : ℝ, 0 < ε →
    ∃ (M : Machine) (Cs Cc Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (h l : ℕ), 0 < h → 0 < l → ∀ I : Tree l h,
      ComputesPrefix M I.encode (bits l I.value.val)
        (Cs * (1 + log₂ (I.encode.length + 2)))
        (exp₂ (Cc * (1 + log₂ (I.encode.length + 2)) ^ ε))
        (Ct * (I.encode.length + 2 : ℝ) ^ q) := by sorry

end CatalyticTreeEval.Main
