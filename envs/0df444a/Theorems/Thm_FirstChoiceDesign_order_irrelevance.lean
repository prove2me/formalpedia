-- Prove2me | Theorems.Thm_FirstChoiceDesign_order_irrelevance
-- name    : FirstChoiceDesign.order_irrelevance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:44.343252+00:00
-- url     : https://prove2.me/theorems/f2210c8f-1925-476a-abb1-74a7620e7550
-- title:
--   Definition 7, p.46 — order irrelevance: $\mathtt{2STAGES}(r)$ produces $\varphi(r)$
-- statement:
--   By McVitie and Wilson's order irrelevance result, the two-stage algorithm of Definition 7, which removes the pivot students $i_0(r),i_1(r)$, runs DA on the rest, and then lets them in, produces the same matching as $\varphi(r)$:
--
--   $$
--   \mathtt{2STAGES}(r)=\varphi(r).
--   $$
--
--   The result allows the pivot students' effect to be studied in isolation.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - encoding: any lottery number profile r → Tieless r, not required Consistent with the regime; reason: the proof of Theorem 1 uses the statement at such profiles; consistent profiles are a special case
--   - encoding: the case i₀(r) = i₁(r) = ∅, where the permutations are the identity → a pivot pair is a hypothesis; reason: in the omitted case the claim is trivial or has no meaning
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Definition 7, p.46 (McVitie and Wilson, 1970)

import Definitions.Def_FirstChoiceDesign_IsPivot
import Definitions.Def_FirstChoiceDesign_twoStages

namespace FirstChoiceDesign

/-- Order irrelevance, Definition 7, Cowles Foundation DP No. 2056R, p.46: by McVitie and Wilson (1970),
`2STAGES(r)` and `φ(r)` produce the same matching.

**Formalization Note** The case `i₀(r) = i₁(r) = ∅` removes nobody, and then `2STAGES(r)` is `φ(r)`
by construction, so the statement is for a pivot pair. `r` need not be consistent with the regime. -/
theorem order_irrelevance {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m)
    (hr : Tieless r) (s : Fin m) (i₀ i₁ : Fin n) (hp : IsPivot φ X s r i₀ i₁) :
    twoStages φ X r i₀ i₁ = outcome φ X.toSetting X.ρ r := by sorry

end FirstChoiceDesign
