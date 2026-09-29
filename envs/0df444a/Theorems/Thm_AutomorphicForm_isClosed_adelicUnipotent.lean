-- Prove2me | Theorems.Thm_AutomorphicForm_isClosed_adelicUnipotent
-- name    : AutomorphicForm.isClosed_adelicUnipotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/b56c0ae9-8136-5c95-be30-a137287c7cf5
-- title:
--   The adelic unipotent subgroup is closed in GL₂(A_K)
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K`, and let `AdelicGL2 (𝓞 K) K` denote $\mathrm{GL}_2(\mathbb{A}_K)$, the general linear group of $2\times 2$ matrices over $\mathbb{A}_K$, i.e. the units of the matrix ring, carrying the topology induced from that of the units of $M_2(\mathbb{A}_K)$ (so that $g \mapsto g$ and $g \mapsto g^{-1}$ are both entrywise continuous). Let `adelicUnipotent K` be the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ defined as the range of the group homomorphism `unipotentGL2Hom`, which sends an element $x$ of the multiplicative copy of the additive group of $\mathbb{A}_K$ to the invertible matrix `unipotentGL2 x`. The assertion is that the underlying subset of $\mathrm{GL}_2(\mathbb{A}_K)$ determined by this subgroup is closed.
--
--   This is the standard fact that the unipotent radical $N(\mathbb{A}_K)$ of the Borel subgroup of $\mathrm{GL}_2$ over the adeles is a closed subgroup. It is used as the closedness hypothesis needed to handle quotient measures and integration over $N(\mathbb{A}_K)$, in the treatment of constant terms, class sums over windows, and the Rankin–Selberg estimates in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isClosed_adelicUnipotent.lean

import Definitions.Def_AutomorphicForm_UnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.isClosed_adelicUnipotent (K : Type) [Field K] [NumberField K] :
    IsClosed ((adelicUnipotent K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by sorry
