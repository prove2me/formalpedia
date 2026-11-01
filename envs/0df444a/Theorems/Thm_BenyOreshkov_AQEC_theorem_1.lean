-- Prove2me | Theorems.Thm_BenyOreshkov_AQEC_theorem_1
-- name    : BenyOreshkov.AQEC.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:11.204982+00:00
-- url     : https://prove2.me/theorems/593e78e1-00b5-4117-b33f-59ec3e42a09b
-- title:
--   Theorem 1 — $\max_{\mathcal R}F(\mathcal R\mathcal N,\mathcal M)=\max_{\mathcal R'}F(\widehat{\mathcal N},\mathcal R'\widehat{\mathcal M})$ for complementary channels
-- statement:
--   Let $A$, $B$, $E$, $B'$, $E'$ be finite-dimensional Hilbert spaces with $A\neq 0$. Let $\mathcal N$ be a channel from $A$ to $B$ with complementary channel $\widehat{\mathcal N}$ from $A$ to $E$, and $\mathcal M$ a channel from $A$ to $B'$ with complementary channel $\widehat{\mathcal M}$ from $A$ to $E'$ (each pair given by one isometry, $A\to B\otimes E$ and $A\to B'\otimes E'$). With $F$ the worst-case entanglement fidelity of Eq. (2),
--   $$
--   \max_{\mathcal R} F(\mathcal R\mathcal N,\mathcal M) = \max_{\mathcal R'} F(\widehat{\mathcal N},\mathcal R'\widehat{\mathcal M}),
--   $$
--   where $\mathcal R$ ranges over all quantum channels from $B$ to $B'$ and $\mathcal R'$ over all quantum channels from $E'$ to $E$. Both maxima are attained.
--
--   The theorem turns the search for a recovery channel $\mathcal R$ that makes $\mathcal R\mathcal N$ close to $\mathcal M$ into a dual search for a channel $\mathcal R'$ that makes $\mathcal R'\widehat{\mathcal M}$ close to the complementary channel $\widehat{\mathcal N}$. For $\mathcal M=\mathrm{id}$, $\widehat{\mathcal M}$ is the trace, and exact correctability becomes the condition that $\widehat{\mathcal N}$ is constant: the Knill–Laflamme conditions.
--
--   **Formalization Note** "max" is stated as: both sets of values have a greatest element and the two greatest elements are one number $v$. Channels are finite normalized Kraus families; $F$ is the infimum over density matrices of the root-fidelity entanglement fidelity, with the canonical purification.
--
--   Differences from the source:
--   - reading: max_R F(RN, M) = max_R′ F(N̂, R′M̂) → ∃ v, v is the greatest element of {F(R ∘ N, M) : R channel} and of {F(N̂, R′ ∘ M̂) : R′ channel}; reason: "max" asserts attainment; this is the stronger reading (attainment and equality, not only equal suprema)
--   - encoding: min_ρ F_ρ → infimum over density matrices; reason: the minimum exists (compact set, continuous function), same value
--   - encoding: |ψ⟩ any purification of ρ → the canonical purification ψ_ρ(r, a) = (√ρ)_{ar}, reference first; reason: F_ρ does not depend on the purification
--   - encoding: f(ρ, σ) = Tr √(√ρ σ √ρ) → QAlgorithms.rootFidelity with cfc Real.sqrt; reason: this is the positive square root on the positive semidefinite arguments that occur
--   - encoding: quantum channels → finite normalized Kraus families (QAlgorithms.IsChannel); reason: in finite dimension these are exactly the CPTP maps
--   - encoding: N̂ complementary to N → one isometry V : A → B ⊗ E with N = Tr_E(V·V†), N̂ = Tr_B(V·V†), E any finite type; reason: the source's definition of complementary channels
--   - encoding: input space of positive dimension → [Nonempty A]; reason: for A of dimension zero there are no states, and the maxima in (3) can be over an empty set of channels (B nonzero, B′ zero), so (3) is undefined; for A nonzero the isometries force B, E, B′, E′ nonzero
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, Theorem 1, Eq. (3), p. 2

import Definitions.Def_BenyOreshkov_AQEC_IsComplementaryPair
import Definitions.Def_BenyOreshkov_AQEC_worstFid

open Matrix QAlgorithms

namespace BenyOreshkov.AQEC

/-- **Theorem 1**, Eq. (3), Bény, Oreshkov, *General conditions for approximate quantum error
correction and near-optimal recovery channels*, arXiv:0907.5391v4, p. 2: "If N̂ and M̂ are
channels complementary to N and M, respectively, then max_R F(RN, M) = max_R′ F(N̂, R′M̂), where
the maxima are over all quantum channels with the appropriate source and target spaces."

For channels `N : A → B` and `M : A → B′` with complementary channels `N̂ : A → E` and
`M̂ : A → E′`, the worst-case entanglement fidelity `F(R ∘ N, M)` over all channels `R : B → B′`
and `F(N̂, R′ ∘ M̂)` over all channels `R′ : E′ → E` both attain their maxima, and the two maxima
are one number `v`.

**Formalization Note** "max" is `IsGreatest` with one common value (Reading 1); `F` is
`worstFid` (the infimum over density matrices of the root-fidelity entanglement fidelity,
Readings 2–4); channels are finite normalized Kraus families, `QAlgorithms.IsChannel`
(Reading 5); complementarity is one isometry for both channels (Reading 6). `[Nonempty A]`
excludes only the zero-dimensional input, where (3) can be a maximum over an empty set of
channels (Reading 7). -/
theorem theorem_1 {A B E B' E' : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Fintype E]
    [DecidableEq E] [Fintype B'] [DecidableEq B'] [Fintype E'] [DecidableEq E']
    (N : Superop A B) (Nc : Superop A E) (M : Superop A B') (Mc : Superop A E')
    (hN : IsComplementaryPair N Nc) (hM : IsComplementaryPair M Mc) :
    ∃ v : ℝ,
      IsGreatest {x : ℝ | ∃ R : Superop B B', IsChannel R ∧ x = worstFid (R ∘ N) M} v ∧
      IsGreatest {x : ℝ | ∃ R' : Superop E' E, IsChannel R' ∧ x = worstFid Nc (R' ∘ Mc)} v := by sorry

end BenyOreshkov.AQEC
