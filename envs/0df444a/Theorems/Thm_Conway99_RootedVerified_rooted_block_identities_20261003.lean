-- Prove2me | Theorems.Thm_Conway99_RootedVerified_rooted_block_identities_20261003
-- name    : Conway99.RootedVerified.rooted_block_identities_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-03T08:16:13.155975+00:00
-- url     : https://prove2.me/theorems/39a5c111-5d4b-4cbd-b428-84ee46ec9734
-- title:
--   Necessary rooted block identities for an SRG(99,14,1,2)
-- statement:
--   Let $G$ be a finite simple strongly regular graph with parameters $(99,14,1,2)$, and let $r$ be any vertex. Thus $G$ has 99 vertices, every vertex has degree 14, adjacent vertices have one common neighbor, and distinct nonadjacent vertices have two common neighbors. Write $A$ for the integer adjacency matrix. Let $L=N_G(r)$ and $F=V\setminus(\{r\}\cup L)$, and define $A_F=A[F,F]$, $N=A[F,L]$, and $M=A[L,L]$. Let $I_F$ be the identity matrix on $F$, and let $J_{X,Y}$ denote the all-ones matrix on $X\times Y$. Then all three identities hold:
--
--   $$
--   \begin{aligned}
--   A_FN+NM+N&=2J_{F,L},\\
--   A_F^2+A_F+NN^{\mathsf T}&=12I_F+2J_{F,F},\\
--   \sum_{w\in F}(A_F)_{xw}&=12\quad\text{for every }x\in F.
--   \end{aligned}
--   $$
--
--   The graph-owned blocks have sizes $84\times84$, $84\times14$, and $14\times14$ under these hypotheses. These are necessary restrictions on any hypothetical graph with Conway's parameters. They establish neither a construction nor nonexistence, and do not establish a converse from a fixed-label matrix encoding to a graph.
-- source:
--   Local source: Conway99/Conway99/Verified/Rooted.lean at rooted-bridge lane commit 688f16d30aaf045040290462f60369db373fbe5b, declarations Conway99.RootedVerified.transport, far_quadratic, and far_degree. Graph-owned definitions are extracted from Conway99.Core. Consolidated standalone source: prove2me/RootedBridge.lean, SHA-256 817c75531a9be7c498b143f3db1e6a06cfb8c208416ec30d7e638cedd18505c5. Context is the public Conway99.conway_99 target at https://prove2.me/theorems/7bc34ad9-a7f2-480e-ac84-4cfe4cd5042a; these necessary identities do not solve that target.

import Definitions.Def_Conway99_Rooted_Blocks_20261003
set_option autoImplicit false
open Matrix Finset

theorem Conway99.RootedVerified.rooted_block_identities_20261003 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (h : G.IsSRGWith 99 14 1 2) :
    (Conway99.Rooted.AFar G r * Conway99.Rooted.NReg G r +
      Conway99.Rooted.NReg G r * Conway99.Rooted.MMate G r +
      Conway99.Rooted.NReg G r =
      2 • Conway99.allOnes (Conway99.Rooted.FarT G r) (Conway99.Rooted.LocT G r) ℤ) ∧
    (Conway99.Rooted.AFar G r ^ 2 + Conway99.Rooted.AFar G r +
      Conway99.Rooted.NReg G r * (Conway99.Rooted.NReg G r)ᵀ =
      12 • (1 : Matrix (Conway99.Rooted.FarT G r) (Conway99.Rooted.FarT G r) ℤ) +
      2 • Conway99.allOnes (Conway99.Rooted.FarT G r) (Conway99.Rooted.FarT G r) ℤ) ∧
    (∀ x : Conway99.Rooted.FarT G r,
      (∑ w : Conway99.Rooted.FarT G r, Conway99.Rooted.AFar G r x w) = 12) := by sorry
