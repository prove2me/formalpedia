-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_lemma_4_8
-- name    : AffinePolicyOpt.OneDim.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:08:07.067107+00:00
-- url     : https://prove2.me/theorems/14acbeb4-c851-4b52-b224-dfb218a04c0c
-- title:
--   Lemma 4.8, p. 22 — the affine cost coefficients satisfy h(b₀ + Σ_{j∈S} b_j) ≤ z₀ + Σ_{j∈S} z_j for every index set S
-- statement:
--   Let $k\ge0$ and let $a,b\in\mathbb R^{k+1}$ (generators $1,\dots,k+1$) satisfy $b_j>0$ and $a_1/b_1>\dots>a_{k+1}/b_{k+1}$; let $b_0\in\mathbb R$ and let $h:\mathbb R\to\mathbb R$ be convex. Write $v_j$ for the vertex with $\pi_2[v_j]=b_0+b_1+\dots+b_j$ and $h(v_j)=h(b_0+\dots+b_j)$. Let $0=s(1)<s(2)<\dots<s(n)=k+1$ be matched indices, and let $z_0,z_1,\dots,z_{k+1}$ and $K_{s(2)},\dots,K_{s(n)}$ satisfy
--
--   1. (51), matching: $z_0+z_1+\dots+z_{s(i)}=h(v_{s(i)})$ for all $i$;
--   2. (51), alignment: $(z_j+a_j)/b_j=K_{s(i+1)}$ for $s(i)<j\le s(i+1)$;
--   3. (52): $K_{s(2)}\ge\dots\ge K_{s(n)}$;
--   4. (53): for $s(i)<j<s(i+1)$,
--   $$\frac{h(v_j)-h(v_{s(i)})+a_{s(i)+1}+\dots+a_j}{b_{s(i)+1}+\dots+b_j}\le K_{s(i+1)}\le\frac{h(v_{s(i+1)})-h(v_j)+a_{j+1}+\dots+a_{s(i+1)}}{b_{j+1}+\dots+b_{s(i+1)}}.$$
--
--   Then for every set $S\subseteq\{1,\dots,k+1\}$ of indices,
--   $$h\Big(b_0+\sum_{j\in S}b_j\Big)\le z_0+\sum_{j\in S}z_j.$$
--
--   This is the vertex form of the robust domination of the convex stage cost by the affine cost of Algorithm 2; Lemma 4.9 extends it to the whole hypercube.
--
--   **Formalization Note** The page states the lemma for "the coefficients computed in Algorithm 2"; the Lean statement takes the system (51)–(53), which the proof shows Algorithm 2's output satisfies, as hypotheses, with all fractions cross-multiplied (the denominators are positive sums of $b$'s). Two misprints of (53) are corrected: the upper bound of the first block sums up to $s(2)$ (printed $s(1)$), and the general block uses $K_{s(i+1)}$. The page's "$\forall j(1),\dots,j(m)$" is read as a set of distinct indices (with repeated indices the inequality can fail); the empty set, which the page excludes, is included and is just $h(b_0)\le z_0$. The hypothesis $b_j>0$ is added: the page divides by $b_j$ in (48), (51), (53) and (56). Indices are stored 0-based, and the matched indices $s(1),\dots,s(n)$ are Lean's `s 0, …, s n`.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 22, Lemma 4.8 and (51)–(53); Algorithm 2 and System (48), p. 20

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

namespace AffinePolicyOpt.OneDim

/-- Lemma 4.8: if the coefficients `z_0, z_1, …, z_{k+1}` satisfy the matching and alignment
equations (51), the ordering (52) and the inequalities (53) (corrected), then
`h(b_0 + Σ_{j ∈ S} b_j) ≤ z_0 + Σ_{j ∈ S} z_j` for every set `S` of generator indices. -/
theorem lemma_4_8 (k : ℕ) (b0 : ℝ) (a b : Fin (k + 1) → ℝ) (hb : ∀ g, 0 < b g)
    (hab : GenOrdered a b) (h : ℝ → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (z0 : ℝ) (z : Fin (k + 1) → ℝ)
    (n : ℕ) (s : Fin (n + 1) → ℕ) (hs : StrictMono s) (hs0 : s 0 = 0)
    (hsn : s (Fin.last n) = k + 1) (K : Fin n → ℝ)
    -- (51), matching
    (h51m : ∀ i, z0 + psum z 0 (s i) = h (b0 + psum b 0 (s i)))
    -- (51), alignment, cross-multiplied
    (h51a : ∀ i : Fin n, ∀ g : Fin (k + 1), s i.castSucc ≤ (g : ℕ) → (g : ℕ) < s i.succ →
      z g + a g = K i * b g)
    -- (52)
    (h52 : Antitone K)
    -- (53), cross-multiplied
    (h53 : ∀ i : Fin n, ∀ j : ℕ, s i.castSucc < j → j < s i.succ →
      h (b0 + psum b 0 j) - h (b0 + psum b 0 (s i.castSucc)) + psum a (s i.castSucc) j ≤
          K i * psum b (s i.castSucc) j ∧
        K i * psum b j (s i.succ) ≤
          h (b0 + psum b 0 (s i.succ)) - h (b0 + psum b 0 j) + psum a j (s i.succ)) :
    ∀ S : Finset (Fin (k + 1)), h (b0 + ∑ g ∈ S, b g) ≤ z0 + ∑ g ∈ S, z g := by sorry

end AffinePolicyOpt.OneDim
