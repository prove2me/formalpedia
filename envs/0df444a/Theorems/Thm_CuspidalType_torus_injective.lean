-- Prove2me | Theorems.Thm_CuspidalType_torus_injective
-- name    : CuspidalType.torus_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/402687ba-a830-599b-8586-ac5b5c382f27
-- title:
--   Injectivity of the non-split torus in GL₂(𝔽_q)
-- statement:
--   Let $q$ be a prime. Write $\mathbb{F}_{q^2}$ for `GaloisField q 2`, regarded as an algebra over $\mathbb{Z}/q$, and let `quadBasis q` be the basis of $\mathbb{F}_{q^2}$ over $\mathbb{Z}/q$ indexed by `Fin 2` obtained from the fact that this extension has rank $2$. The homomorphism `torus q` is the map of unit groups induced by the $\mathbb{Z}/q$-algebra homomorphism that sends $\alpha \in \mathbb{F}_{q^2}$ to the matrix, with respect to `quadBasis q`, of the $\mathbb{Z}/q$-linear endomorphism $x \mapsto \alpha x$ of $\mathbb{F}_{q^2}$; thus `torus q` is a monoid homomorphism from $\mathbb{F}_{q^2}^\times$ to `GL2 q`, the group of invertible $2\times 2$ matrices over $\mathbb{Z}/q$. The assertion is that the underlying function of `torus q` is injective: if two units $\alpha, \beta \in \mathbb{F}_{q^2}^\times$ have the same matrix of multiplication in the chosen basis, then $\alpha = \beta$.
--
--   This identifies $\mathbb{F}_{q^2}^\times$ with its image, the non-split (elliptic) maximal torus of $\mathrm{GL}_2(\mathbb{F}_q)$, so that the image has exactly $q^2-1$ elements. It is used in [`CuspidalType.NV3Arch.sum_elliptic_eq`](thm.html#CuspidalType.NV3Arch.sum_elliptic_eq), in the counting of elliptic conjugacy classes entering the cuspidal-type analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_torus_injective.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.torus_injective (q : ℕ) [Fact q.Prime] : Function.Injective (torus q) := by sorry
