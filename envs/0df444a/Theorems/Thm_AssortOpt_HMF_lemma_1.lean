-- Prove2me | Theorems.Thm_AssortOpt_HMF_lemma_1
-- name    : AssortOpt.HMF.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:19.773378+00:00
-- url     : https://prove2.me/theorems/1488897a-acfb-4f3b-b877-ab39164f2027
-- title:
--   Lemma 1, p. 19 (corrected: S ⊆ {j : φ_j ≡ 1}) — REV[φ] − REV[S] is the sum over S-disjoint prefixes of r^S(ρ) Pr[ρ] times the stopping indicator
-- statement:
--   Let $\mathcal L, p$ be a list distribution with prices $r_j \ge 0$, let $\phi$ be a monotone stopping policy, and let $S$ be an assortment such that $\phi_j$ is the all-1 function for every $j \in S$. Then
--   $$\mathsf{REV}[\phi] - \mathsf{REV}[S] = \sum_{\rho : \rho \cap S = \emptyset} r^S(\rho) \Pr[\rho]\, \phi_{\rho_{\mathrm{end}}}(\rho_{\mathrm{pre}}) \prod_{k=1}^{|\rho|-1} \big(1 - \phi_{\rho_k}(\rho_{1:k-1})\big), \qquad (14)$$
--   the sum over nonempty realizable prefixes disjoint from $S$, where $r^S(\rho)$ is the $S$-adjusted price (13).
--
--   The product term is $1$ exactly when $\phi$ stops on $\rho$ after not stopping before, so the lemma says that $\phi$'s advantage over $S$ is the expected $S$-adjusted price of the prefix it stops on. It is the identity that turns the comparison of a policy with an assortment into a sign question about adjusted prices.
--
--   **Formalization Note** The sum runs over `prefixes D` (the nonempty realizable prefixes) filtered by disjointness from $S$; unrealizable prefixes have $\Pr[\rho] = 0$ on the page and contribute nothing.
--
--   Differences from the source:
--   - correction: "for any monotone stopping policy $\phi$ and assortment $S$" → additionally $\phi_j(H) = 1$ for every $j \in S$ and $H \not\ni j$; reason: false as printed: MNL with $n = 3$ and all weights $1$, $r = (1,2,3)$, $\phi \equiv 0$ (monotone), $S = \{1\}$ gives $\mathsf{REV}[\phi] - \mathsf{REV}[S] = -1/2$ while the right side of (14) is $0$. The proof (p. 40) uses that "$\phi$ would have stopped on the first intersection with $S$", which holds when every $\phi_j$, $j \in S$, is the all-1 function, the choice of $S$ in the proof of Theorem 2 (p. 43).
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - encoding: the sum over prefixes $\rho$ with $\rho \cap S = \emptyset$ → the sum over nonempty realizable prefixes disjoint from $S$; reason: other prefixes have $\Pr[\rho] = 0$, and $r^S(\rho)$ is defined only for realizable $\rho$ (Definition 12).
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 19, Lemma 1 (14); proof on p. 40

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem lemma_1 {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (φ : Policy n) (hφ : IsMonotonePolicy φ) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → φ j H = true) :
    revPolicy D r φ - revAssort D r S =
      ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
        adjPrice D r S ρ * prefProb D ρ * stopInd φ ρ := by sorry

end AssortOpt.HMF
