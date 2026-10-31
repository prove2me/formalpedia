-- Prove2me | Theorems.Thm_EdgeworthCore_lemma_2_1
-- name    : EdgeworthCore.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:53.073815+00:00
-- url     : https://prove2.me/theorems/ce4834fb-bcb1-4fed-810d-7782af3b07fe
-- title:
--   Lemma 2.1 — every $h$-core allocation of the replica economy $\mathcal E^n$ has the equal treatment property
-- statement:
--   Let $\mathcal E=((u_t,\omega_t))_{t\in[h]}$ be an exchange economy with $\ell$ goods in which every utility $u_t$ is strictly monotonic, continuous and strictly concave on $\mathbb R^\ell_+$, and let $n\in\mathbb N$. Let $X=(X_{i,t})_{i\in[n],\,t\in[h]}$ be an allocation of the replica economy $\mathcal E^n$ that lies in the $h$-core of $\mathcal E^n$, i.e. no coalition of at most $h$ consumers of $\mathcal E^n$ blocks it. Then $X$ has the equal treatment property:
--   $$X_{i,t}=X_{i',t}\qquad\text{for every }t\in[h]\text{ and all }i,i'\in[n].$$
--
--   This strengthens the classical observation of Debreu and Scarf, stated for the core (the $nh$-core), to coalitions of size $h$. It justifies representing core allocations of $\mathcal E^n$ by vectors in $\mathbb R^{h\ell}_+$, one bundle per type.
--
--   **Formalization Note** Only the lemma's own hypotheses are assumed; no differentiability, Lipschitz bound or normalization. Consumers of $\mathcal E^n$ are the pairs $(i,t)$.
--
--   Differences from the source:
--   - encoding: u_t : ℝ^ℓ_+ → ℝ strictly monotonic, continuous, strictly concave → total function on EuclideanSpace ℝ (Fin ℓ) with these three properties on ℝ^ℓ_+; reason: only values on ℝ^ℓ_+ enter; same instances
--   - encoding: S-allocation (y_i)_{i∈S} with no stated sign → y_i ∈ ℝ^ℓ_+; reason: u_i(y_i) is defined only on ℝ^ℓ_+ (p.5)
-- source:
--   Barman–Echenique, arXiv:1905.05165v1, §2, Lemma 2.1 (Equal treatment property), p.7 (proof Appendix C, p.26)

import Mathlib
import Definitions.Def_EdgeworthCore_Model

namespace EdgeworthCore

/-- **Lemma 2.1** (Equal treatment property; Barman–Echenique, arXiv:1905.05165v1, §2, p.7; proof
in Appendix C, p.26). Let the utilities `u_t` of an exchange economy `E = ((u_t, ω_t))_{t∈[h]}` be
strictly monotonic, continuous and strictly concave (on `ℝ^ℓ_+`). Then every allocation `X` of the
replica economy `E^n` that lies in the `h`-core of `E^n` has the equal treatment property:
`X_{i,t} = X_{i',t}` for every type `t` and all `i, i' ∈ [n]`.

**Formalization Note.** Only the lemma's own hypotheses are assumed (no differentiability,
Lipschitz bound or normalization). `X` is an arbitrary allocation of `E^n`, indexed by
`Fin n × Fin h`; coalitions of `E^n` are nonempty `Finset`s of consumers of cardinality at most `h`.
-/
theorem lemma_2_1 {h ℓ : ℕ} (E : Economy (Fin h) ℓ)
    (hmono : ∀ t, StrictlyMonotone (E.u t))
    (hcont : ∀ t, ContinuousOn (E.u t) (orthant ℓ))
    (hconc : ∀ t, StrictConcaveOn ℝ (orthant ℓ) (E.u t))
    (n : ℕ) (X : Fin n × Fin h → Bundle ℓ) (hX : InKappaCore (replica E n) h X) :
    EqualTreatment X := by sorry

end EdgeworthCore
