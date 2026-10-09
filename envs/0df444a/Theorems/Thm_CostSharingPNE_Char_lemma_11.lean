-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_11
-- name    : CostSharingPNE.Char.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:37.841066+00:00
-- url     : https://prove2.me/theorems/60cc2999-c407-49fd-bf51-a465d4d91397
-- title:
--   Lemma 11, p. 54 — the transitive closure ⪰⁺_Ω is a partial order on N: i ⪰⁺_Ω j and j ⪰⁺_Ω i imply i =⁺_Ω j
-- statement:
--   Let $\mathbb W$ be a set of local welfare functions on $N=\{1,\dots,n\}$, $n>1$, and let $f^{\mathbb W}$ be budget-balanced distribution rules that guarantee equilibrium existence in all games $G\in\mathcal G(N,f^{\mathbb W},\mathbb W)$ and are described completely by a sequence of weight systems $\Omega=\{\omega^{W,T}\}$:
--   $$
--   f^W(i,S)=\sum_{T\in\mathcal T^W} q^W_T\, f^T_{GWSV}[\omega^{W,T}](i,S)\qquad(W\in\mathbb W,\ i\in S).
--   $$
--   Define on $N$ the relations (74): $i\succeq_\Omega j$ if there are $W\in\mathbb W$ and $T\in\mathcal T^{W+}_{ij}$ with $i\in S_1^{W,T}$, or $i=j$; and $i=_\Omega j$ if $i\succeq_\Omega j$ and $j\succeq_\Omega i$. Let $\succeq^+_\Omega$ and $=^+_\Omega$ be their transitive closures. Then $\succeq^+_\Omega$ constitutes a partial order on $N$, in the sense of the proof: for all $i,j\in N$,
--   $$
--   i\succeq^+_\Omega j\ \text{ and }\ j\succeq^+_\Omega i\ \Longrightarrow\ i=^+_\Omega j .
--   $$
--
--   The equivalence classes of $=^+_\Omega$, ordered by $\succeq^+_\Omega$, become the blocks of the universal weight system.
--
--   **Formalization Note** $\succeq^+_\Omega$ is reflexive and transitive by construction; the page's "partial order" is the antisymmetry modulo $=^+_\Omega$ shown in the proof (literal antisymmetry $i=j$ is false: two players sharing a block are related both ways). $S_1^{W,T}$ is read on $T$ as the positive-share block $\overline T$ of $T$ under $\omega^{W,T}$, and $\mathcal T^{W+}_{ij}$ as the coalitions of $\mathcal T^W_{ij}$ in which $i$ or $j$ lies in $\overline T$ — under the displayed representation these are the coalitions where $i$ or $j$ gets a positive share, as in (53).
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 11 and (74), p. 54

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_11 (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ 𝕎, IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE 𝕎 f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S) :
    ∀ i j : Fin n, Relation.TransGen (succeq 𝕎 Ω) i j → Relation.TransGen (succeq 𝕎 Ω) j i →
      Relation.TransGen (eqOmega 𝕎 Ω) i j := by sorry

end CostSharingPNE.Char
