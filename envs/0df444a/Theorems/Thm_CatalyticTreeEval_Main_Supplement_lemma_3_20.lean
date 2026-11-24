-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_lemma_3_20
-- name    : CatalyticTreeEval.Main.Supplement.lemma_3_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:37:21.541908+00:00
-- url     : https://prove2.me/theorems/8707797e-3d94-4d76-84d0-a0c2dfc912f6
-- title:
--   Lemma 3.20 (used in the proof of Theorem 3.4) — uniform full-residue decoder
-- statement:
--   For every odd prime $m$ supplied as input, there are $k\le m$ shifts and term functions forming a decoder for the entire residue set $A=\mathbb Z_m$, with a single term printer, uniform over $m$, using
--   $$\operatorname{space}_{\mathrm{term}}\le C L(m).$$
--   For every nonzero $a\in\mathbb Z_m$ and every $z\in\mathbb Z_m$, its terms obey $\sum_{j<k}\varphi_j(z+ab_j)=0$, while $\sum_{j<k}\varphi_j(0)=1$. The printer outputs both $b_j$ and $\varphi_j(z)$ on request. This full-residue decoder supports the squared-distance ordinary-space construction.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: binary parameters and one-based finite indices → self-delimiting binary headers, zero-based Fin indices and the published printer requests; reason: encodes the same finite data with linear bit-length overhead and no change to the space class
--   - encoding: log m → L(m); reason: equivalent up to an absolute constant on odd primes m≥3
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Lemma 3.20, printed p. 20 (PDF p. 22)

import Definitions.Def_CatalyticTreeEval_Main_Decoder

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem lemma_3_20 :
    ∃ (MD : Machine) (C : ℝ), 0 < C ∧
      ∀ m : ℕ, Nat.Prime m → Odd m → ∃ k : ℕ, k ≤ m ∧
      ∃ D : Decoder m k, IsDecoder Set.univ D ∧
        DecoderAccess MD (natCode m) D (C * lg m) := by sorry

end CatalyticTreeEval.Main.Supplement
