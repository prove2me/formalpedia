-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_eq_25
-- name    : BicliqueSDP.Chain.eq_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:33.396325+00:00
-- url     : https://prove2.me/theorems/4502b7a0-f81c-4d3d-afe2-3349ecc909e1
-- title:
--   Eq. (25), p. 12 — las₁(G) = ϑ(G) for every graph G
-- statement:
--   Let $G=(V,E)$ be any finite graph. The first Lasserre bound
--   $$\mathrm{las}_1(G)=\max\Bigl\{\mathrm{Tr}(X):\begin{pmatrix}1&\mathrm{diag}(X)^{\mathsf T}\\ \mathrm{diag}(X)&X\end{pmatrix}\succeq0,\ X_{ij}=0\text{ for }\{i,j\}\in E\Bigr\}$$
--   and Lovász's theta number
--   $$\vartheta(G)=\max\{\langle J,X\rangle: X\succeq0,\ \mathrm{Tr}(X)=1,\ X_{ij}=0\text{ for }\{i,j\}\in E\}$$
--   coincide:
--   $$\mathrm{las}_1(G)=\vartheta(G).$$
--
--   The paper calls this well known and refers to Grötschel, Lovász and Schrijver; it is used in §3.3 to pass between the two formulations of $\vartheta$ in the proofs of $h_1(G)\le\frac14\alpha(G)$ and $g_1(G)\le\alpha(G)h_1(G)$.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 12, Eq. (25)

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- Eq. (25) (p. 12): for every finite graph `G`, `las₁(G) = ϑ(G)`. -/
theorem eq_25 {V : Type} [Fintype V] (G : SimpleGraph V) : las1 G = theta G := by sorry

end BicliqueSDP.Chain
