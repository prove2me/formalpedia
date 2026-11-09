-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_21
-- name    : ChvatalOneHard398.SAT.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:35.862509+00:00
-- url     : https://prove2.me/theorems/76e6586f-8159-428f-80ee-a0a80c0f0901
-- title:
--   Lemma 21 — properties of the residue formulation
-- statement:
--   Let $m,m'\ge1$, $D\ge2$, $h\ge1$, and let $p_1,\ldots,p_s\ge2$ be pairwise coprime with $\Pi=\prod_jp_j\ge2^h$ and $p_{\max}=\max_jp_j$. Let $H\in\{0,\ldots,D-1\}^{m'\times m}$, $t\in\mathbb Z^m$, $M=\Lambda_D^\perp(H)$, and $d=Ht\bmod D$.
--   Let $X=X(p,h,H,D,t)$ be the three-part construction, and let $c_i$, $V_i=\sum_{j,a}\iota_j a x_{i,j,a}$ and $\kappa_i$ be its recorded linear functions. Then
--
--   $$c_i(x)=V_i(x)-\Pi\kappa_i(x),\quad0\le c_i(x)\le2^h-1,\quad (Hc(x)-d)/D=\zeta(x)\qquad(x\in X),$$
--
--   for a vector of integral linear functions $\zeta$. The integral points of $X$ correspond bijectively to $(t+M)\cap\{0,\ldots,2^h-1\}^m$. Its concrete exact-one family is well formed, with at most $\max\{9,p_{\max}\}$ literals per row. It has at most $C=6m(\sum_jp_j)(\lfloor\log_2\Pi\rfloor+2)+6m'mh(\lfloor\log_2D\rfloor+2)$ functional constraints. This family is computed in the stated polynomial time and supplies the rank argument with identities valid at fractional points.
--
--   Differences from the source:
--   - encoding: time polynomial in m,m′,Σp,log D and the encoding size of t → unary m,m′,p,h and binary D,H,t as encParams; reason: h≤log₂Π≤Σp on valid parameters, so input length is polynomially equivalent to the printed numerical parameters
--   - encoding: deterministic polynomial time in structured bit size → TM2 polynomial time with fixed, dimension-prefixed, length-framed binary encodings; reason: these encodings are injective and have length linear in the corresponding bit size
--   - encoding: real coordinate vectors, integer points, and lattice notation → Fin-indexed real coordinates, explicit integer-point predicates, and Euclidean integer column spans; reason: these represent the same vectors and full-rank lattices; norms on lattices are Euclidean
--   - encoding: O(m(Σp)log Π+m′mh log D) constraints → C=6m(Σp)(Nat.log 2 Π+2)+6m′mh(Nat.log 2 D+2); reason: p.24 applies Lemma 20 m times with k=Σp,K=Π and m′ times with k=mh,K=D; each minimal L is at most Nat.log 2 K+2
--   - encoding: CRT representatives ι and d in their specified residue intervals → extended-gcd CRT coefficients and least nonnegative residues; reason: valid parameters make these the unique representatives specified in §5.3
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.23, Lemma 21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT
open scoped BigOperators

theorem lemma_21 :
    PolyTime encParams encFormula (fun a => functionalExact (residueSystem a).model) ∧
    ∀ a : Params, a.Valid →
      (∀ x ∈ residuePoly a, ∀ i,
        residueC a x i = residueV a x i - (a.prod : ℝ)*evalLinear ((residueSystem a).kappa[i.val]!) x ∧
        0 ≤ residueC a x i ∧ residueC a x i ≤ (2 : ℝ)^a.h-1) ∧
      (∃ zeta : Fin a.r → IntLinear, ∀ x ∈ residuePoly a, ∀ r,
        ((∑ i, (a.H r i : ℝ)*residueC a x i) - a.d r)/(a.D : ℝ) = evalLinear (zeta r) x) ∧
      Nonempty (integralPoints (residuePoly a) ≃ residueCandidates a) ∧
      residuePoly a = exactOne (functionalExact (residueSystem a).model) ∧
      (functionalExact (residueSystem a).model).WellFormed ∧
      (∀ T ∈ (functionalExact (residueSystem a).model).clauses, T.card ≤ max 9 a.pmax) ∧
      (residueSystem a).model.gates.length ≤ gateBound a := by sorry

end ChvatalOneHard398.SAT
