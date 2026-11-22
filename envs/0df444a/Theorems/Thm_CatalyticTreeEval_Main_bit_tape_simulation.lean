-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_bit_tape_simulation
-- name    : CatalyticTreeEval.Main.bit_tape_simulation
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:00:13.372638+00:00
-- url     : https://prove2.me/theorems/2a10a6e4-6c26-4355-9cd3-e0d4772e1d01
-- title:
--   Remark 3.3 — uniform exact simulation of registers by arbitrary catalytic bits
-- statement:
--   There is a uniform finite-table transformation of register machines into machines acting on arbitrary binary catalyst tapes, together with absolute positive constants $C_s,C_c,C_t$ and a positive integer $q$.
--
--   Fix a valid Section 4 frame $F$. Suppose that on a fixed input, a machine $M$ writes the same prescribed output and restores every initial triple of registers over $\mathbb Z_m$, in dimension $\max(d,\lceil\ell/\lfloor\log_2m\rfloor\rceil)$, using at most $S$ work bits and $T$ steps. Then the transformed machine computes the same output for **every** initial bitstring of sufficient length, restores every bit exactly, and never addresses beyond the rounded catalyst bound. Its simultaneous bounds are
--
--   $$
--   \begin{aligned}
--   \mathrm{free}&\le C_s(S+s+1),\\
--   \mathrm{catalytic}&\le C_c\,d\bigl(1+\log_2(dm)\bigr),\\
--   \mathrm{time}&\le C_t\bigl(T+(2^s+1)^q\bigr).
--   \end{aligned}
--   $$
--
--   The construction implements Remark 3.3. It partitions the used tape prefix into $3\,\mathrm{paddedDimension}(F)$ widened blocks, finds a common shift making all blocks valid, updates only their residue parts while freezing their quotient parts, and subtracts the shift at the end. Arbitrary initial block patterns are therefore allowed. The simulation also supports any longer catalyst by preserving and ignoring the unused suffix. The padded dimension covers the zero-extension vectors supplied by the Section 4.3 readout, while the $O(d\log(dm))$ catalyst and additive $\operatorname{poly}(2^s)$ preprocessing costs include this extension. The shift and the small fixed number of erased original register blocks account for the additive $O(s)$ workspace.
--
--   The interface leaves all semantic input and output strings unchanged, charges actual finite-machine transitions and visited work cells, and keeps all constants before the frame, input, and catalyst. It is the single conversion step used to obtain Corollary 4.2 from Theorem 4.1, and is reusable for the corresponding register-to-bit translations in the supplementary framework.
--
--   **Formalization Note** The source's big-O resource bounds are represented by explicit positive constants and upward cell rounding. The guarantee is stated as `ComputesPrefix`, so the entire arbitrary tape is restored and the head bound applies throughout the run, not merely at termination.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Remark 3.3, printed pp. 14–15 (PDF pp. 16–17), proof of Corollary 4.2, printed p. 21 (PDF p. 23), and padding convention in Section 4.3, printed pp. 23–26 (PDF pp. 25–28); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Framework
import Definitions.Def_CatalyticTreeEval_Main_BitRepresentation

set_option autoImplicit false

/-- Uniform shifted-block simulation of padded registers on arbitrary bit tapes. -/
theorem CatalyticTreeEval.Main.bit_tape_simulation :
    ∃ (simulate : Machine → Machine) (Cs Cc Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (F : Frame), F.valid →
      ∀ (M : Machine) (input output : List Bool) (S T : ℝ),
        0 ≤ S → 0 ≤ T →
        (∀ R : Registers F.m (paddedDimension F),
          RegisterComputes M input output R S T) →
        ComputesPrefix (simulate M) input output
          (Cs * (S + F.s + 1))
          (Cc * F.d * (1 + log₂ (F.d * F.m)))
          (Ct * (T + ((2 : ℝ) ^ F.s + 1) ^ q)) := by sorry
