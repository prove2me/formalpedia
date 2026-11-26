-- Prove2me | Theorems.Thm_BranchActualQ_large_scale_positive_from_explicit_inputs
-- name    : BranchActualQ.large_scale_positive_from_explicit_inputs
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T18:24:18.57058+00:00
-- url     : https://prove2.me/theorems/e4955df3-cf51-46db-8114-a9ad96492661
-- title:
--   Original Q: eventual positivity along large-scale subsequences from explicit analytic inputs
-- statement:
--   Let $\xi(s)=(1+s(s-1)\Lambda_0(s))/2$, where $\Lambda_0$ is the completed zeta function with its poles removed, and index each upper-half-plane zero with its analytic multiplicity. Set $B_i=-(\rho_i-1/2)^2$, $\gamma_i=\operatorname{Im}\rho_i$, and
--   \[
--   G(x)=\operatorname{Re}\xi(1/2+\sqrt{x}),\qquad
--   Q_n(u)=2^n u^{2n-1}(-1)^{n-1}\frac{d^n}{dx^n}\bigl(\log G(x)-\log G(0)\bigr)\bigg|_{x=u^2}.
--   \]
--   Assume $\gamma_i\ge2$; every occurrence with $\gamma_i\le1000$ is critical; an occurrence satisfies $\gamma_i\le100$; finite occurrence counts below $\gamma_i^2\le y$ are bounded by $C y^{3/4}$ for all $y\ge1$; and $G(x)/G(0)=\prod_i(1+x/B_i)$ for all $x>0$.
--   For natural orders $k_j\to\infty$ and positive $u_j$ such that $k_j/u_j^2\to\infty$, one has $Q_{k_j}(u_j)>0$ for all sufficiently large $j$. The original Q and occurrence multiplicities are unchanged. These analytic inputs are explicit premises; this statement does not discharge them or cover the other scale regimes.
-- source:
--   Desenvolvimento RH, 2026-11-17. Uses BranchAnchorRepair.spectral_sum_eventually_positive_from_counting, already ACCEPTED. The original xi/occurrence/Q definitions and full analytic proof of the spectral identity are reproduced from the existing accepted spectral-identity work (BranchActualQ.spectral_identity_small_scale_and_first_order; work/qbridge/modular.lean). No modification to the Bible or PDFs; standard Mathlib analytic identities and prior project proofs retain their role.

import Mathlib
open Filter Topology

theorem BranchActualQ.large_scale_positive_from_explicit_inputs :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // f s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt f s.val)
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    (∀ i : I, 2 ≤ i.1.val.im) →
    (∀ i : I, i.1.val.im ≤ 1000 → i.1.val.re = 1/2) →
    (∃ i : I, i.1.val.im ≤ 100) →
    ∀ C : ℝ,
    (∀ y ≥ (1 : ℝ), ∀ F : Finset I,
      (∀ i ∈ F, i.1.val.im^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4)) →
    (∀ x > 0, ((G x/G 0 : ℝ) : ℂ) =
      ∏' i : I, (1+(x : ℂ)/(-(i.1.val-1/2)^2))) →
    ∀ (k : ℕ → ℕ), Tendsto k atTop atTop →
    ∀ (u : ℕ → ℝ), (∀ j, 0 < u j) →
    Tendsto (fun (j : ℕ) => (k j : ℝ)/(u j)^2) atTop atTop →
    ∀ᶠ j : ℕ in atTop, 0 < Q (k j) (u j) := by sorry
