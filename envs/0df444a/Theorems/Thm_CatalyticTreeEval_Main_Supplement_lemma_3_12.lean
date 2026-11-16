-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_lemma_3_12
-- name    : CatalyticTreeEval.Main.Supplement.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:35:40.319366+00:00
-- url     : https://prove2.me/theorems/4a47e7be-e318-4825-9e8f-3051ba87f5b7
-- title:
--   Lemma 3.12 (used in the proof of Theorem 3.4) — uniform squared-distance matching vectors
-- statement:
--   Let $M,w$ be positive integers and $m>wM^2$ an odd prime, all supplied as input. Put $N=M^w$ and $S=\{0,1,\ldots,wM^2\}\subseteq\mathbb Z_m$. There is an $S$-matching-vector family $U,V$ of exact size $N$ in dimension $w+2$, and a single fixed printer, uniform over all these parameters, with
--   $$\operatorname{space}_{\mathrm{print}}\le C\bigl(L(N)+L(m)\bigr).$$
--   The printer receives the parameters and the requested indices and outputs both full vectors. This squared-distance construction supports the ordinary-space algorithms. The domain includes $M=1$ and does not impose the stronger inequality $m>2wM^2$.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: binary parameters and one-based finite indices → self-delimiting binary headers, zero-based Fin indices and the published printer requests; reason: encodes the same finite data with linear bit-length overhead and no change to the space class
--   - encoding: log N+log m → L(N)+L(m); reason: the positive-log convention includes the singleton family M=1 with the same O(log N+log m) bound since m≥3
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Lemma 3.12, printed p. 17 (PDF p. 19)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem lemma_3_12 :
    ∃ (MV : Machine) (C : ℝ), 0 < C ∧
      ∀ M w m : ℕ, 0 < M → 0 < w → Nat.Prime m → Odd m → w * M ^ 2 < m →
      ∃ U V : Fin (M ^ w) → Vec m (w + 2),
        SMatching (intervalScores m (w * M ^ 2)) U V ∧
        VectorAccess MV (natsCode [M,w]) U V (C * (lg (M ^ w) + lg m)) := by sorry

end CatalyticTreeEval.Main.Supplement
