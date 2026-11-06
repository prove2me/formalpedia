-- Prove2me | Theorems.Thm_FewExperts_eq_18_19_epoch_potential
-- name    : FewExperts.eq_18_19_epoch_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:19.533467+00:00
-- url     : https://prove2.me/theorems/52f7ec16-94da-4f94-8935-b5f1e8dcabfb
-- title:
--   §4.2, (18)–(19) — a run that does not fail raises $S$ by $\ge\alpha\ell/2$; any run lowers $S$ by $\le\alpha\ell/8$
-- statement:
--   For all sufficiently large $N$ and $T$ and every scale $L\ge L_0$, set $\eta=8s/L$, $\ell=L/(64rs)$, $q=\alpha/(2^{10}r)$ and $m=\lceil4r/q\rceil$. Let $a_0$ be the shifted advantages at the start of an epoch and $\mathcal D(i)\propto e^{-\eta a_0^i}$. Let $G^{\mathcal A},G^{\mathcal B},G^i$ be the interval gains, up to a time $t$ of the run, of the run, the baseline and each expert, so that the shifted advantages at $t$ are $a^i=a_0^i+G^{\mathcal A}-G^i$. Suppose that:
--
--   1. the set $J$ of experts violating (16), $G^{\mathcal B}\ge G^i-2\sqrt{T\ln m}$, has $\mathcal D(J)\le q$;
--   2. $G^i-G^{\mathcal A}\le2r(\ell+1)$ for every expert $i$ (Proposition 2 (i)).
--
--   Then, with $S$ the softmin at rate $\eta$:
--
--   $$
--   G^{\mathcal A}-G^{\mathcal B}\ge\alpha\ell-16\sqrt T\ \Longrightarrow\ S(a)-S(a_0)\ge\frac{\alpha\ell}{2}, \tag{18}
--   $$
--   $$
--   G^{\mathcal A}-G^{\mathcal B}\ge-16\sqrt T\ \Longrightarrow\ S(a)-S(a_0)\ge-\frac{\alpha\ell}{8}. \tag{19}
--   $$
--
--   These two bounds are the per-epoch progress and loss of the potential.
--
--   Differences from the source:
--   - generalization: the quantities of an actual run at time t (a₀, interval gains of 𝒜, ℬ and the experts, J_t) → arbitrary reals and an arbitrary set J satisfying the hypotheses the derivation uses; reason: every run supplies such quantities, so the statement specializes to the paper's
--   - reading: if 𝒜 does not fail (property (ii)) / if 𝒜 fails (property (iii)) → the hypotheses G^𝒜 − G^ℬ ≥ αℓ − 16√T, respectively ≥ −16√T; reason: these are exactly the bounds the paper substitutes into (17)
--   - encoding: floors and ceilings omitted (p.13): 1/α levels, m = 4r/q, 2r scales, 2⁹rs/α epochs → K = ⌊1/α⌋ levels (exponent 1/α − j read as K − j), m = ⌈4r/q⌉, ⌈2r⌉ scales, ⌈2⁹rs/α⌉ epochs per scale; reason: the paper omits them where they do not materially affect the analysis; the floor keeps the top threshold Kαℓ ≤ ℓ, which Proposition 2 (i) uses
--   - encoding: T and N sufficiently large (convention of §3, p.13, for everything outside §3) → ∃ N₀ T₀, ∀ N ≥ N₀, ∀ T ≥ T₀; reason: the paper's own convention made explicit
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §4.2, (17)–(19), pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_FewExperts_fewExpertsAlg

namespace FewExperts

/-- **§4.2, (17)–(19): one epoch moves the potential.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §4.2, pp.21–22 (PDF 22–23), (17), (18), (19): "If A does not fail, property (ii)
gives G^A_{(t0,t]} − G^B_{(t0,t]} ≥ αℓ − 16√T, … Consequently, S_t − S_{t0} ≥ αℓ/2. (18) … On the
other hand, if A fails, we still have the bound from property (iii) of A, which tells us that
G^A_{(t0,t]} − G^B_{(t0,t]} ≥ −16√T. … Hence S_t − S_{t0} ≥ −αℓ/8. (19) The same bound holds at
every time during the run."

For `N`, `T` large enough and every scale `L ≥ L₀`, with `η = 8s/L`, `ℓ = L/(64rs)`,
`q = α/(2¹⁰r)`, `m = ⌈4r/q⌉`: let `a₀` be the shifted advantages at the epoch's start `t0` and
`𝒟(i) ∝ exp(−η a₀^i)`; let `G^A`, `G^B`, `G^i` be the interval gains on `(t0, t]` of the run `A`,
of the baseline `B` and of each expert, so that the shifted advantages at `t` are
`a^i = a₀^i + G^A − G^i`. Suppose that the experts `J` for which (16)
`G^B ≥ G^i − 2√(T ln m)` fails have `𝒟(J) ≤ q`, and that Proposition 2 (i) holds:
`G^i − G^A ≤ 2r(ℓ + 1)` for all `i`. Then, with `S = softmin_η`:

* (18): if `G^A − G^B ≥ αℓ − 16√T` (A does not fail), then `S(a) − S(a₀) ≥ αℓ/2`;
* (19): if `G^A − G^B ≥ −16√T` (property (iii)), then `S(a) − S(a₀) ≥ −αℓ/8`.

**Formalization Note** The statement is about the quantities the proof feeds in, at an arbitrary
time `t` of the run; the inequality `2√(T ln m) + 16√T ≤ αℓ/16`, which the paper derives from the
choice of `L₀`, is not assumed but follows from `L ≥ L₀`. "Sufficiently large" (p.13) is
`∃ N₀ T₀`. -/
theorem eq_18_19_epoch_potential :
    ∃ N₀ T₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → T₀ ≤ T → ∀ L : ℝ, L0 N T ≤ L →
    ∀ (a0 Gi : Fin N → ℝ) (GA GB : ℝ) (J : Finset (Fin N)),
      ∑ i ∈ J, boostDist (etaOf N L) a0 i ≤ qParam N T →
      (∀ i ∉ J, Gi i - 2 * Real.sqrt (T * Real.log (mParam N T)) ≤ GB) →
      (∀ i, Gi i - GA ≤ 2 * rT T * (ellOf N T L + 1)) →
      (alpha N T * ellOf N T L - 16 * Real.sqrt T ≤ GA - GB →
          alpha N T * ellOf N T L / 2 ≤
            softmin (etaOf N L) (fun i => a0 i + GA - Gi i) - softmin (etaOf N L) a0) ∧
      (-(16 * Real.sqrt T) ≤ GA - GB →
          -(alpha N T * ellOf N T L / 8) ≤
            softmin (etaOf N L) (fun i => a0 i + GA - Gi i) - softmin (etaOf N L) a0) := by sorry

end FewExperts
