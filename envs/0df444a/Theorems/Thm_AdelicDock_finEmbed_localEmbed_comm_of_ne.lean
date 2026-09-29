-- Prove2me | Theorems.Thm_AdelicDock_finEmbed_localEmbed_comm_of_ne
-- name    : AdelicDock.finEmbed_localEmbed_comm_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/51f9d02b-9a19-555c-81a5-ef618e094e9e
-- title:
--   Placements at distinct finite places commute in GL₂ of the adeles
-- statement:
--   Let $R$ be a commutative ring which is a Dedekind domain, $K$ a field which is an $R$-algebra and a fraction field of $R$, and let $v,w$ be points of the height-one spectrum of $R$ with $v \neq w$. Let $x \in \mathrm{GL}_2(K_v)$ and $y \in \mathrm{GL}_2(K_w)$, where $K_v$ denotes `v.adicCompletion K`. For a place $u$, `localEmbed R K u` is the monoid homomorphism $\mathrm{GL}_2(K_u) \to \mathrm{GL}_2(\mathbb{A}_{K,\mathrm{fin}})$ built from `localMat R K u`, which sends a matrix $g$ to the matrix of finite adeles whose $(i,j)$ entry is the splice at $u$ of the $(i,j)$ entry of the identity matrix with $g_{ij}$; and `finEmbed R K` is the monoid homomorphism $\mathrm{GL}_2(\mathbb{A}_{K,\mathrm{fin}}) \to \mathrm{GL}_2(\mathbb{A}_K)$ attaching the identity matrix as archimedean component entrywise. The assertion is that the images of $x$ and of $y$ under $u \mapsto$ `finEmbed R K ∘ localEmbed R K u` commute: their product in either order agrees in $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the elementary fact that elements of an adelic group supported at distinct finite places commute, multiplication in the restricted product being componentwise. It is used in the construction of automorphic-form level structures, namely by [`AutomorphicForm.exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime`](thm.html#AutomorphicForm.exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdelicDock_finEmbed_localEmbed_comm_of_ne.lean

import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain

theorem AdelicDock.finEmbed_localEmbed_comm_of_ne {R : Type*} {K : Type*} [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {v w : HeightOneSpectrum R} (hvw : v ≠ w)
    (x : GL (Fin 2) (v.adicCompletion K)) (y : GL (Fin 2) (w.adicCompletion K)) :
    finEmbed R K (localEmbed R K v x) * finEmbed R K (localEmbed R K w y) =
      finEmbed R K (localEmbed R K w y) * finEmbed R K (localEmbed R K v x) := by sorry
