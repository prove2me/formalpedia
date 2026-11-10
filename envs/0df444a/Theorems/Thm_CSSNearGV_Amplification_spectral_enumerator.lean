-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_spectral_enumerator
-- name    : CSSNearGV.Amplification.spectral_enumerator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:31.860224+00:00
-- url     : https://prove2.me/theorems/0051b382-d930-4f70-b122-3f3e42055275
-- title:
--   Proposition 3.3 — actual expected enumerators and spectral bounds
-- statement:
--   For fixed even $s\ge2$ and $m\ge0$, uniformly in all weights $0\le c\le n=sb$,
--   $$W_{AD}^{(m)}(c)\le\operatorname{poly}(n)2^{n r_{AD}^{(m)}(c/n)},\qquad
--   W_{DA}^{(m)}(c)\le\operatorname{poly}(n)2^{n r_{DA}^{(m)}(c/n)}.$$
--   The enumerators are expectations of the actual random codes. The two convolution identities (3)–(4) hold for these expectations, and the feasible maxima in Definition 3.2 are attained.
--
--   This bridges the finite ensemble and its continuous spectral bounds.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
--   - encoding: maxima and inverse-entropy root used in Definitions 1.2 and 3.2–3.4 → supremum/infimum definitions with attainment and the root property included as conclusions; reason: well-posedness is proved rather than assumed or silently delegated to total-function defaults
--   - encoding: Proposition 3.3 together with Equations (3)-(4) → the spectral bounds and the exact enumerator recurrences in one conjunction; reason: the additional clauses restate the cited source identities for the actual ensemble
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Proposition 3.3, Definition 3.2 and Equations (3)–(4), printed pp.8–10 / PDF 10–12

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem spectral_enumerator (s : ℕ) (hs : 2 ≤ s) (he : Even s) :
  (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ q N : ℕ,
    ∀ b c : ℕ, 1 ≤ b → N ≤ s * b → c ≤ s * b → ∀ ad : Bool,
      enumerator s b m ad c ≤ C * (s * b : ℝ) ^ q *
        (2 : ℝ) ^ ((s * b : ℝ) * shapePair s ad m ((c : ℝ) / (s * b)))) ∧
  (∀ b m c : ℕ, 1 ≤ b → c ≤ s * b → ∀ ad : Bool,
    enumerator s b (m + 1) ad c =
      ∑ a ∈ Finset.range (s * b + 1), ∑ t ∈ Finset.range (s * b + 1),
        enumerator s b m ad a * transition (s * b) ad a t * transition (s * b) (!ad) t c) ∧
  (∀ m : ℕ, ∀ ad : Bool, ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∃ α β : ℝ,
    domainPair ad α β γ ∧ shapePair s ad (m + 1) γ = shapePair s ad m α + fPair ad α β γ ∧
    ∀ a t : ℝ, domainPair ad a t γ →
      shapePair s ad m a + fPair ad a t γ ≤ shapePair s ad (m + 1) γ) := by sorry

end CSSNearGV.Amplification
