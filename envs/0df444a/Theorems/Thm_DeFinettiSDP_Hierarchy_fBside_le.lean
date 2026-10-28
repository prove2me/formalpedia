-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_fBside_le
-- name    : DeFinettiSDP.Hierarchy.fBside_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:40.638603+00:00
-- url     : https://prove2.me/theorems/4a64085d-f589-43a1-8296-f42a6e693902
-- title:
--   §2.4, p. 6 — the minimal distortion with side information satisfies f(B|·) ≤ d_B²(d_B+1)
-- statement:
--   For every system $B$ of positive dimension $d_B\ge1$, the minimal distortion with side information (10),
--
--   $$f(B|\cdot)=\inf_{\mathcal M_B}\ \sup_{\substack{\xi_{AB}^\dagger=\xi_{AB}\\ \xi_A=0,\ \xi_B=0}}\frac{\|\xi_{AB}\|_1}{\|(\mathcal I_A\otimes\mathcal M_B)(\xi_{AB})\|_1},$$
--
--   with the infimum over all measurements on $B$ and the supremum over all finite-dimensional systems $A$ and Hermitian $\xi_{AB}$ with vanishing marginals, satisfies
--
--   $$f(B|\cdot)\ \le\ d_B^2(d_B+1).$$
--
--   This is the dimension-dependent constant that enters the explicit convergence rate of the SDP hierarchy (Theorem 3.1).
--
--   **Formalization Note** $f(B|\cdot)$ is valued in $[0,\infty]$. The hypothesis $d_B\ge1$ records that the paper's system $B$ has positive dimension.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §2.4, p. 6, eq. (10) and the last display of the page (proved via Lemma D.1)

import Mathlib
import Definitions.Def_DeFinettiSDP_Hierarchy_Distortion
open Matrix

namespace DeFinettiSDP.Hierarchy

/-- **f(B|·) ≤ d_B²(d_B + 1)** (arXiv:1810.12197v3, §2.4, p. 6, last display): the minimal
distortion with side information (10) of a positive-dimensional system is at most
`d_B² (d_B + 1)`. -/
theorem fBside_le : ∀ dB : ℕ, 1 ≤ dB →
    fBside dB ≤ (dB : ENNReal) ^ 2 * ((dB : ENNReal) + 1) := by sorry

end DeFinettiSDP.Hierarchy
