-- Prove2me | Theorems.Thm_DirKECC1549_Asm_big_K
-- name    : DirKECC1549.Asm.big_K
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T05:25:00.31464+00:00
-- url     : https://prove2.me/theorems/3981afec-b82d-4666-8529-c8e03980f668
-- title:
--   Large exponent: every d below m fails
-- statement:
--   If $nm<K$ and $d<m$ then $n d^K<m^K$ (Bernoulli's inequality for $m^K$ against $(m-1)^K$).
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of the exact computation of $\Delta=\max\{k-1,\lceil m/n^{\varepsilon_k}\rceil\}$ (Algorithm 3, line 6; the child contract `delta_impl`): with $K=2^{k-1}$, the ceiling is the least $d$ with $m^K\le n d^K$, decided with multi-word integers in base $2^b>n+m$ (limbs of $K+2$ words), or equal to $m$ when $K>nm$.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_DMath

set_option autoImplicit false
open Finset
open DirKECC1549.Main
open DirKECC1549 DirKECC1549.Asm

theorem DirKECC1549.Asm.big_K (n m K d : ℕ) (hK : n * m < K) (hd : d < m) : n * d ^ K < m ^ K := by sorry
