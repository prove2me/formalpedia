-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_5_9
-- name    : BlottoFPTAS.Main.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:43:41.159307+00:00
-- url     : https://prove2.me/theorems/0a9726f1-e173-405f-b879-140a253fe809
-- title:
--   Lemma 5.9 — S_out cell-midpoint shifts change P(X_j < t) and P(X_j ≤ t) by at most 1/S_out
-- statement:
--   In the setting of Lemma 5.8 (light battlefields replaced), fix a reduced allocation $x$ spending at most one and a light battlefield $j$. Replacing the uniform shift $\omega\sim\mathrm{Unif}[0,1)$ by $\omega_\ell$ for a uniformly random $\ell\in\{0,\dots,S_{\mathrm{out}}-1\}$ changes each of the probabilities $P(X_j<t)$ and $P(X_j\le t)$ by at most $1/S_{\mathrm{out}}$, for every bid amount $t\ge0$:
--   $$\Big|\,\mathrm{Leb}\{\omega\in[0,1):X_j(\omega)<t\}-\tfrac1{S_{\mathrm{out}}}\#\{\ell:X_j(\omega_\ell)<t\}\Big|\le\tfrac1{S_{\mathrm{out}}},$$
--   and the same with $\le t$. This lets the sampler use exactly $\log_2S_{\mathrm{out}}$ random bits for the shift.
--
--   Differences from the source:
--   - generalization: w′ the weights of the first rounding → any positive integer weights w′; reason: the lemma uses only that p_j = w′_j/W_G with integers; the rounding output is a special case
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 44, Lemma 5.9

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_Reduction

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma 5.9** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 44).
In the replaced case, fix a reduced allocation `x` (spending at most one) and a light battlefield
`j`. Replacing the uniform shift `ω ∼ Unif[0, 1)` by `ω_ℓ` for a uniformly random
`ℓ ∈ {0, …, S_out − 1}` changes each of `P(X_j < t)` and `P(X_j ≤ t)` by at most `1/S_out`, for
every bid amount `t ≥ 0`. -/
theorem lemma_5_9 {n : ℕ} (a : ℕ) (ha : 1 ≤ a) (w' : Fin n → ℕ) (hw' : ∀ j, 1 ≤ w' j)
    (hrep : Replaced a w') (x : Fin (mRed a w') → ℝ) (hx : x ∈ X (mRed a w') 1)
    (j : Fin n) (hj : IsLight a w' j) (t : ℝ) (ht : 0 ≤ t) :
    |((volume.restrict (Set.Ico (0 : ℝ) 1)) {ω | recon a w' x ω j < t}).toReal -
        ((Finset.univ.filter fun ℓ : Fin (Sout a) => recon a w' x (shift a w' ℓ) j < t).card : ℝ) /
          Sout a| ≤ 1 / Sout a ∧
    |((volume.restrict (Set.Ico (0 : ℝ) 1)) {ω | recon a w' x ω j ≤ t}).toReal -
        ((Finset.univ.filter fun ℓ : Fin (Sout a) => recon a w' x (shift a w' ℓ) j ≤ t).card : ℝ) /
          Sout a| ≤ 1 / Sout a := by sorry

end BlottoFPTAS.Main
