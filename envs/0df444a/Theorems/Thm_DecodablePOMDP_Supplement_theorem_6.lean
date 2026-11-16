-- Prove2me | Theorems.Thm_DecodablePOMDP_Supplement_theorem_6
-- name    : DecodablePOMDP.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:46:11.486028+00:00
-- url     : https://prove2.me/theorems/0a175727-d7ea-420b-bbee-1997da019bac
-- title:
--   Theorem 6 — constant $\ell_2$-observability, yet $\Theta(S\log(1/\varepsilon))$ observations to forget the initial belief
-- statement:
--   Let $G=(\mathcal L,\mathcal R,E)$ range over the simple 3-regular bipartite graphs with $|\mathcal L|=|\mathcal R|=n$ whose biadjacency matrix $M$ has second singular value $\sigma_2(M)\le2\sqrt2$, and consider the POMDP of App. C.1 built from $G$: $S=2n$ states, one action, transitions that resample the state uniformly within its group, and observations that reveal a uniformly chosen incident edge with probability $1/2$ and otherwise a group-biased symbol $g_\pm$ with probabilities $\frac14\pm\frac1{8\sqrt n}$. Let $D_h=\mathbb E_{b_0}\|b_h-\widehat b_h\|_1$ be the expected $\ell_1$ distance between the filters started at $b_0=\mathrm{Unif}(\mathcal L)$ and at $\widehat b_0=\frac12\mathrm{Unif}(\mathcal L)+\frac12\mathrm{Unif}(\mathcal R)$, under the true process started at $b_0$.
--
--   There are universal constants $c,C>0$ such that for every such graph:
--
--   1. the observation kernel is $\alpha_0$-$\ell_2$-observable with $\alpha_0=\sqrt{3-2\sqrt2}/6$, independently of $n$;
--   2. for every $\varepsilon\in(0,1/4]$ and every $h$,
--   $$h<c\,S\log(1/\varepsilon)\ \Longrightarrow\ D_h>\varepsilon,\qquad h\ge C\,S\log(1/\varepsilon)\ \Longrightarrow\ D_h\le\varepsilon .$$
--
--   Thus the number of observations needed to bring $D_h$ down to $\varepsilon$ is $\Theta(S\log(1/\varepsilon))$, and constant $\ell_2$-observability does not give a filter-forgetting time polylogarithmic in $S$; this is why the paper's planner avoids filter-stability arguments.
--
--   Differences from the source:
--   - reading: the number of observations required to reduce E‖b_h − b̂_h‖₁ to at most ε is Θ(S log(1/ε)) → ∃ c, C > 0 chosen before n, the graph and ε: ε < D_h for every h < c·S·log(1/ε), and D_h ≤ ε for every h ≥ C·S·log(1/ε), S = 2n; reason: Θ with universal constants, as for the universal constants of Theorem 1; the two-sided threshold at every h implies that the least h with D_h ≤ ε lies in [c S log(1/ε), C S log(1/ε)]
--   - reading: provided the horizon is sufficiently large → no horizon: the stationary kernels are applied h times; reason: the kernels are the same at every stage, so a horizon only needs to be at least h
--   - encoding: constant ℓ2-observability (the channel has ℓ2-observability constant at least √(3 − 2√2)/6, p.25, C.3) → the conjunct `IsL2Observable (obsK M) (√(3 − 2√2)/6)` for every member of the family; reason: the "In particular" sentence refers to this constant, printed on p.25 and proved in C.3
--   - encoding: G chosen from an infinite family of bipartite Ramanujan graphs, M ∈ {0,1}^{n×n}, row and column sums 3, σ₂(M) ≤ 2√2 → every `n` and every `M : Fin n → Fin n → Bool` with all row and column sums 3 and at most one eigenvalue of MᵀM above (2√2)² = 8; reason: these are the properties C.1 names; a 3-regular bipartite graph with σ₂ ≤ 2√2 is exactly a bipartite Ramanujan graph; the existence of infinitely many is cited, not claimed
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 6, p.25 (proof pp.25–26); ℓ2-observability constant p.25 and App. C.3, pp.26–28

import Mathlib
import Definitions.Def_DecodablePOMDP_Supplement_Observability
import Definitions.Def_DecodablePOMDP_Supplement_SlowForgetting

namespace DecodablePOMDP.Supplement

/-- **Theorem 6 (slow filter forgetting under ℓ2-observability).** There are universal constants
`c, C > 0` such that for every member of the family of App. C.1 — every `n` and every biadjacency
matrix `M` of a simple 3-regular bipartite graph on `n + n` vertices with `σ₂(M) ≤ 2√2`, giving the
POMDP with `S = 2n` states, transition kernel `transT n` and observation kernel `obsK M` — the
following hold:
1. the observation kernel is `α₀`-ℓ2-observable with `α₀ = √(3 − 2√2) / 6`, independently of `n`;
2. for every `ε ∈ (0, 1/4]` and every number of observations `h < c · S · log(1/ε)`, the expected
   filter distance satisfies `D_h > ε`;
3. for every `ε ∈ (0, 1/4]` and every `h ≥ C · S · log(1/ε)`, `D_h ≤ ε`.
Here `D_h = E_{b₀} ‖b_h − b̂_h‖₁` compares the filters started at `b₀ = Unif(L)` and
`b̂₀ = ½ Unif(L) + ½ Unif(R)` on the observations of the process started at `b₀`.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), Theorem 6, p.25 (proof pp.25–26; ℓ2-observability in C.3, pp.26–28): "For the
family of POMDPs described above and every 0 < ε ≤ 1/4, the number of observations required to
reduce E_{b0}∥bh − b̂h∥1 to at most ε is Θ(S log(1/ε)), provided the horizon is sufficiently large.
In particular, constant ℓ2-observability does not guarantee a polylogarithmic filter-forgetting
time." With p.25: "The channel K has ℓ2-observability constant at least √(3 − 2√2)/6,
independently of n; see Section C.3."

**Formalization Note.**
* `Θ(S log(1/ε))` is read with universal constants `c, C > 0` chosen before the instance and `ε`
  (uniform in `n`, in the graph and in `ε ∈ (0, 1/4]`): every `h` below `c S log(1/ε)` fails to
  reach `D_h ≤ ε`, every `h` above `C S log(1/ε)` reaches it. `S = 2n`, `log` is natural.
* "provided the horizon is sufficiently large": the kernels are stationary and the filters are run
  for `h` steps, so no horizon appears.
* "constant ℓ2-observability" is the conjunct (1), from p.25 and C.3.
* The family is every `M` with row and column sums `3` and `σ₂(M) ≤ 2√2`; the existence of
  infinitely many such graphs [Marcus et al. 2013] is cited by the paper and not stated. -/
theorem theorem_6 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (n : ℕ) (M : Fin n → Fin n → Bool), IsCubicBiadjacency M →
      SecondSingularValueLE (realBiadj M) (2 * Real.sqrt 2) →
      IsL2Observable (obsK M) (Real.sqrt (3 - 2 * Real.sqrt 2) / 6) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
        (∀ h : ℕ, (h : ℝ) < c * (2 * (n : ℝ)) * Real.log (1 / ε) → ε < filterDist M h) ∧
        (∀ h : ℕ, C * (2 * (n : ℝ)) * Real.log (1 / ε) ≤ (h : ℝ) → filterDist M h ≤ ε) := by sorry

end DecodablePOMDP.Supplement
