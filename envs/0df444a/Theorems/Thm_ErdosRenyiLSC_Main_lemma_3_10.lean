-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_3_10
-- name    : ErdosRenyiLSC.Main.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:35.738252+00:00
-- url     : https://prove2.me/theorems/7a2929b1-3e36-41a6-964f-eb6a73b4d9b7
-- title:
--   Lemma 3.10, pp. 18–19 — self-consistent resolvent equation (3.23)
-- statement:
--   Let $H=(h_{ij})$ be a real symmetric $N\times N$ matrix and $z\in\mathbb C$ with $\operatorname{Im}z>0$. With $G=(H-z)^{-1}$, $m=N^{-1}\operatorname{Tr}G$, $v_i=G_{ii}-m_{\mathrm{sc}}$, $[v]=N^{-1}\sum_iv_i$, $Z_i=\sum^{(i)}_{k,l}(h_{ik}h_{li}-N^{-1}\delta_{kl})G^{(i)}_{kl}$, $\mathcal A_i=N^{-1}\sum_jG_{ij}G_{ji}/G_{ii}$ and $\Upsilon_i=h_{ii}-Z_i+\mathcal A_i$, every diagonal entry satisfies
--   $$G_{ii}=\frac1{-z-m_{\mathrm{sc}}-([v]-\Upsilon_i)}.$$
--
--   This is the self-consistent equation for the diagonal resolvent entries; compared with the defining relation $m_{\mathrm{sc}}=-1/(z+m_{\mathrm{sc}})$ it isolates the error terms $[v]$ and $\Upsilon_i$ that the local law controls.
--
--   **Formalization Note** $Z_i$ is defined by the last expression of (3.15), which equals the partial expectation $\mathbb{IE}_iZ_{ii}$ when all entries have variance $1/N$; with this definition the lemma is deterministic and is stated for every real symmetric matrix.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, pp. 18–19, Lemma 3.10, (3.23)–(3.24), with (3.15)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting
import Definitions.Def_ErdosRenyiLSC_Main_Resolvent

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 3.10, pp. 18–19: the self-consistent resolvent identity (3.23)
`G_ii = 1 / (-z - m_sc - ([v] - Υ_i))`, for every real symmetric matrix and every
spectral parameter in the upper half plane. -/
theorem lemma_3_10 {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : ∀ i j : Fin N, H i j = H j i) (z : ℂ) (hz : 0 < z.im) (i : Fin N) :
    resolvent H z i i = 1 / (-z - msc z - (vAvg H z - Upsilon H z i)) := by sorry

end ErdosRenyiLSC.Main
