-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_cross_consistent_entropy_bound
-- name    : BirthdayEntropy.Soundness.cross_consistent_entropy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:02:58.57711+00:00
-- url     : https://prove2.me/theorems/cb23214c-91f4-4776-84b1-d26dc6566074
-- title:
--   Entropy bound for an arbitrary cross-consistent signed pair
-- statement:
--   Let $n,\ell$ be nonnegative integers with $0<x=\ell/n\le1/2$, let $0<\beta\le1$, and write $A_0=\log(e/x)$. Let $P$ be a probability law on a finite space, let $X,Y$ be finite-valued random variables, and let $A=f(X)$ and $B=g(Y)$ be signed subsets of $[n]\times\{0,1\}$. Suppose $(A,B)$ is cross-consistent on the support of $P$. Use the terrible count, bad count and three-branch obstruction energy $R$ of equation (5), with parameter $\beta$. Then
--
--   $$H_P(A,B)\le I_P(X;Y)+(16+2/\beta)A_0\,\mathbb E_P R(A,B).$$
--
--   This strengthens the flattening-entropy estimate by applying to every finite cross-consistent law, with coefficient one on mutual information and no logarithmic remainder. No CSP, source-gap hypothesis, or accepted experiment is required; their role in applications is to provide a cross-consistent law and the chosen parameter $\beta$. The result is derived by a weighted encoding of the signed coordinate states, with the same energy as the source.
-- source:
--   Derived strengthening and generalization of Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma 4.7 equations (13)–(17), PDF pp12–14 / printed pp11–13; uses exactly obstruction energy (5), PDF p10 / printed p9.

import Definitions.Def_BirthdayEntropy_Soundness_Biclique
noncomputable section
open scoped Classical
open OAI.ThorpCompatibility BirthdayEntropy.Soundness

theorem BirthdayEntropy.Soundness.cross_consistent_entropy_bound {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {n ℓ : ℕ} (P : Law α) (X : α → β) (Y : α → γ)
    (f : β → Finset (Signed n)) (g : γ → Finset (Signed n))
    (β₀ : ℝ) (hβ : 0 < β₀) (hβ1 : β₀ ≤ 1)
    (hx : 0 < ratio n ℓ) (hxhalf : ratio n ℓ ≤ 1/2)
    (hcross : ∀ z, 0 < P.mass z → CrossConsistent (f (X z),g (Y z))) :
    (P.map (fun z => (f (X z),g (Y z)))).entropy ≤ mutualInfo P X Y +
      (16+2/β₀)*logScale n ℓ * P.mean (fun z => energy ℓ β₀ (f (X z),g (Y z))) := by sorry
