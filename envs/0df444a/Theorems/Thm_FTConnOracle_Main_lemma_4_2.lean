-- Prove2me | Theorems.Thm_FTConnOracle_Main_lemma_4_2
-- name    : FTConnOracle.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:44.274805+00:00
-- url     : https://prove2.me/theorems/85f9dae7-5cdc-499b-8171-6efcc82676ef
-- title:
--   Lemma 4.2 (Local amplification) — supports of the rows and columns of Q(S) are Γ(Y_i), Γ(X_i); symmetry forces X_i = Y_i = ∅ or both larger than t
-- statement:
--   Let $n\ge2$, let $B$ be a bipartite graph with left side $[n]$, right side $[r]$, all left degrees equal to $\ell\ge1$ and (4.1) for the parameter $t$. Let $G$ be a graph on $[n]$, $S\subseteq[n]$ and $i\in[r]$, and let $X_i\subseteq S$, $Y_i\subseteq S^c$ be as defined (vertices of $S$ with a $G$-neighbour in $T_i\cap S^c$, resp. vertices of $S^c$ with a $G$-neighbour in $T_i\cap S$). Then:
--
--   1. (a) $\Gamma(Y_i)=\{j\in[r]:Q(S)_{i,j}>0\}$ and $\Gamma(X_i)=\{j\in[r]:Q(S)_{j,i}>0\}$;
--   2. (b) if $Q(S)$ is symmetric, then $\Gamma(X_i)=\Gamma(Y_i)$, and consequently either $X_i=Y_i=\emptyset$, or $|X_i|>t$ and $|Y_i|>t$:
--
--   $$Q(S)^{\mathsf T}=Q(S)\ \Longrightarrow\ \Gamma(X_i)=\Gamma(Y_i)\ \wedge\ \big(X_i=Y_i=\emptyset\ \vee\ (|X_i|>t\wedge|Y_i|>t)\big).$$
--
--   Local amplification is the step from one crossing edge to many in the proof of cut amplification (Lemma 4.3).
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
--   - encoding: B as a bipartite graph / its r × n incidence matrix with 0/1 columns b_v; Q(S) an r × r matrix → B : Fin n → Finset (Fin r) (right neighbourhoods); b_v = col B v ∈ ℤ^r; Q(S) a Matrix (Fin r) (Fin r) ℤ, symmetric meaning Qᵀ = Q; reason: same objects; integer entries as in the paper
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 17 (PDF 19), Lemma 4.2

import Mathlib
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-- Lemma 4.2 (local amplification, p. 17): for a graph `G` on `[n]`, `S ⊆ [n]` and `i ∈ [r]`,
(a) `Γ(Y_i) = {j : Q(S)_{i,j} > 0}` and `Γ(X_i) = {j : Q(S)_{j,i} > 0}`;
(b) if `Q(S)` is symmetric then `Γ(X_i) = Γ(Y_i)`, and either `X_i = Y_i = ∅` or
`|X_i| > t` and `|Y_i| > t`. -/
theorem lemma_4_2 {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (i : Fin r) :
    (nbhd B (Yset B G S i) = Finset.univ.filter (fun j => 0 < cutMatrix B G S i j) ∧
      nbhd B (Xset B G S i) = Finset.univ.filter (fun j => 0 < cutMatrix B G S j i)) ∧
    ((cutMatrix B G S).transpose = cutMatrix B G S →
      nbhd B (Xset B G S i) = nbhd B (Yset B G S i) ∧
        ((Xset B G S i = ∅ ∧ Yset B G S i = ∅) ∨
          (t < (Xset B G S i).card ∧ t < (Yset B G S i).card))) := by sorry

end FTConnOracle.Main
