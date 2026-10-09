-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_3_4
-- name    : ErdosRenyiLSC.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:43.853988+00:00
-- url     : https://prove2.me/theorems/9379b29e-e036-4a39-a1bc-6fa363bf55e0
-- title:
--   Lemma 3.4, p. 16 — resolvent identities (3.12)–(3.13) for minors
-- statement:
--   Let $H=(h_{ij})$ be a real symmetric $N\times N$ matrix, let $z\in\mathbb C$ with $\operatorname{Im}z>0$, and write $G=(H-z)^{-1}$ and $G^{(\mathbb T)}$ for the resolvent of the minor of $H$ with the rows and columns in $\mathbb T$ removed. Then:
--
--   1. for all $i,j\ne k$,
--   $$G_{ij}=G^{(k)}_{ij}+\frac{G_{ik}G_{kj}}{G_{kk}};$$
--   2. for all $i\ne j$, $G_{ij}=-G_{ii}G^{(i)}_{jj}(h_{ij}-Z_{ij})$;
--   3. for all $i$, $G_{ii}=(h_{ii}-z-Z_{ii})^{-1}$,
--
--   where $Z_{ij}=\sum^{(ij)}_{k,l}h_{ik}G^{(ij)}_{kl}h_{lj}$ is the sum over $k,l\notin\{i,j\}$ (so $Z_{ii}$ uses the minor $G^{(i)}$).
--
--   These Schur-complement identities express resolvent entries through resolvents of minors, which are independent of a row and column of $H$; every later estimate on $G$ starts from them.
--
--   **Formalization Note** The identities are stated for every real symmetric matrix, not only for the random matrices of Definition 2.1; $\operatorname{Im}z>0$ makes every resolvent and every minor resolvent invertible.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 16, Lemma 3.4, (3.12)–(3.14)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting
import Definitions.Def_ErdosRenyiLSC_Main_Resolvent

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 3.4, p. 16: the resolvent identities (3.12) and (3.13) for minors, for every
real symmetric matrix and every spectral parameter in the upper half plane. -/
theorem lemma_3_4 {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : ∀ i j : Fin N, H i j = H j i) (z : ℂ) (hz : 0 < z.im) :
    (∀ i j k : Fin N, i ≠ k → j ≠ k →
      resolvent H z i j =
        minorG H {k} z i j + resolvent H z i k * resolvent H z k j / resolvent H z k k) ∧
    (∀ i j : Fin N, i ≠ j →
      resolvent H z i j =
        -(resolvent H z i i) * minorG H {i} z j j * ((H i j : ℂ) - Zpair H z i j)) ∧
    (∀ i : Fin N,
      resolvent H z i i = ((H i i : ℂ) - z - Zpair H z i i)⁻¹) := by sorry

end ErdosRenyiLSC.Main
