-- Prove2me | Theorems.Thm_DirKECC1549_Asm_residual_cut
-- name    : DirKECC1549.Asm.residual_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T07:02:21.287026+00:00
-- url     : https://prove2.me/theorems/b4cf3ce0-44b8-42fe-a273-242f16376306
-- title:
--   No residual edge leaves the visited set: it is a cut of the flow value
-- statement:
--   If $F$ is a unit flow of value $q$ from $u$ to $v$ and the set $S\ni u$, $v\notin S$, has no residual edge leaving it (every flow-free edge leaving $S$ and every flow edge entering $S$ is absent), then $\mathrm{out}(S)=q$.
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of Lemma 3 of the paper (Ford–Fulkerson with at most $k$ augmentations, the platform theorem `lemma_3_flow`): starting from the empty flow, each round runs a breadth-first search from $z$ in the residual graph (flow edges reversed, scanned through the out-adjacency array for edges without flow and the in-adjacency array for edges with flow); if $r$ is reached, the flow bits along the parent trail from $r$ back to $z$ are toggled, otherwise the visited set is a cut of the current flow value. After at most $k$ rounds the program outputs $q=\min\{k,\lambda(z,r)\}$ and the residual graph, in $O(k(m+n))$ ticks.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_FlowMath

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem DirKECC1549.Asm.residual_cut (D : Fin m → Fin n × Fin n) (u v : Fin n) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v q) (S : Finset (Fin n)) (hu : u ∈ S) (hv : v ∉ S)
    (hcl : ∀ e, (flipEdges D F e).1 ∈ S → (flipEdges D F e).2 ∈ S) : outCount D S = q := by sorry
