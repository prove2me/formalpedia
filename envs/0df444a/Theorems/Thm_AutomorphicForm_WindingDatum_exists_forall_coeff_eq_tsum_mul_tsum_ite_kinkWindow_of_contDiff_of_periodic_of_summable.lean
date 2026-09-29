-- Prove2me | Theorems.Thm_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable
-- name    : AutomorphicForm.WindingDatum.exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/9e8cc886-b572-51f9-a814-03710c70885e
-- title:
--   Kink-window lattice sums realised as winding-datum coefficients
-- statement:
--   Fix natural numbers $r,d,c,A,q$. Let $\Lambda$ be an additive subgroup of $(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,d\to\mathbb Z)$ carrying the discrete topology, let $s$ be an $\mathbb R$-linear form on $\mathbb R^r$ and $\omega\in\mathbb R^d$ with $\omega\neq 0$, such that $s(\gamma_1)=\sum_i\omega_i\gamma_{2,i}$ for every $\gamma=(\gamma_1,\gamma_2)\in\Lambda$; let $\chi:\Lambda\to(\mathbb R/\mathbb Z)^c$ be a group homomorphism admitting a map $\mathrm{lift}$ on the ambient group with values in $\mathbb R^c$ whose reduction modulo $1$ agrees with $\chi$ on $\Lambda$ coordinatewise. Fix slot maps $kC:\mathrm{Fin}\,c\to\mathrm{Fin}\,r$ and $kR:\mathrm{Fin}\,q\to\mathrm{Fin}\,r$, and, for each shape $a\in\mathrm{Fin}\,A$, complex-valued functions $B_a$, $C_{a,k}$ ($k\in\mathrm{Fin}\,q$), $E_{a,j}$ ($j\in\mathrm{Fin}\,c$) on $\mathbb R^r\times\mathbb R^c$, all smooth ($C^\infty$ over $\mathbb R$), all invariant under $\theta\mapsto\theta+\mathrm{Pi.single}\,j\,1$ for each $j$, and all vanishing at $(x,\theta)$ whenever $x\notin S$, where $S\subseteq\mathbb R^r$ is a fixed compact set. Finally fix data indexed by $i\in\mathbb N$: subgroups $\mathrm{sub}_i\le\Lambda$, shapes $\mathrm{shape}(i)\in\mathrm{Fin}\,A$, weights $\mathrm{lam}_i\in\mathbb C$ with $\sum_i\|\mathrm{lam}_i\|<\infty$, and shifts $x^0_i\in\mathbb R^r$, $n^0_i\in\mathbb Z^d$, $\theta^0_i\in\mathbb R^c$. The assertion is that there exists a winding datum $\mathcal A$ of signature $(r,d,c)$ — a `WindingDatum` structure, bundling a discrete subgroup with a product formula as above, a character into $(\mathbb R/\mathbb Z)^c$, subgroups $\mathrm{sub}_i$ of it, continuous integrable windows $\Psi_i$ on $\mathbb R^r$ satisfying, together with their Fourier transforms, the decay bounds $C_i\prod_k(1+|x_k|)^{-2}$, angular frequencies $m_i\in\mathbb Z^c$, phases, base points and weights — such that for every $n\in\mathbb Z^d$ its coefficient $\mathcal A.\mathrm{coeff}(n)=\sum_i'\mathcal A.\mathrm{lam}_i\sum_{\gamma\in\mathcal A.\mathrm{sub}_i}'\mathcal A.\mathrm{fibreTerm}\,i\,n\,\gamma$ equals
--   $$\sum_{i\in\mathbb N}\mathrm{lam}_i\sum_{\substack{\gamma\in\mathrm{sub}_i\\ \gamma_2+n^0_i=n}}G_{\mathrm{shape}(i)}\bigl(x^0_i+\gamma_1,\ \theta^0_i+\mathrm{lift}(\gamma)\bigr),$$
--   both sums being unconditional sums (`tsum`, the inner one over all of $\mathrm{sub}_i$ with the condition $\gamma_2+n^0_i=n$ imposed by an if-then-else returning $0$ otherwise), where
--   $$G_a(x,\theta)=B_a(x,\theta)+\sum_{k}\bigl|1-e^{x_{kR(k)}}\bigr|\,C_{a,k}(x,\theta)+\sum_j\bigl\|1-e^{x_{kC(j)}/2+2\pi i\theta_j}\bigr\|^2\log\bigl\|1-e^{x_{kC(j)}/2+2\pi i\theta_j}\bigr\|\,E_{a,j}(x,\theta).$$
--   No compatibility between the given $\Lambda,s,\omega,\chi,\mathrm{sub},\mathrm{lam}$ and the corresponding fields of $\mathcal A$ is asserted beyond this identity of coefficient functions.
--
--   This is the realisation step for winding data with kink-type windows: it converts an absolutely weighted countable family of lattice sums of smooth, angle-periodic, compactly $x$-supported windows with the two kink factors $|1-e^{x}|$ and $\|1-e^{x/2+2\pi i\theta}\|^2\log\|1-e^{x/2+2\pi i\theta}\|$ into the coefficient function of a single winding datum. It is used by [`AutomorphicForm.exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted`](thm.html#AutomorphicForm.exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted), where class sums of matching local and archimedean windows must be exhibited as winding-datum coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable.lean

import Definitions.Def_AutomorphicForm_WindingDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.WindingDatum.exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable
    {r d c A q : ℕ}
    (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ γ ∈ Λ, s γ.1 = ∑ i, ω i * (γ.2 i : ℝ))
    (χ : Λ →+ (Fin c → AddCircle (1 : ℝ)))
    (lift : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (hlift : ∀ (γ : (Fin r → ℝ) × (Fin d → ℤ)) (hγ : γ ∈ Λ) (j : Fin c),
      ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j)

    (kC : Fin c → Fin r) (kR : Fin q → Fin r)

    (B : Fin A → (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (C : Fin A → Fin q → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (E : Fin A → Fin c → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hC : ∀ a k, ContDiff ℝ (⊤ : ℕ∞) (C a k))
    (hE : ∀ a j, ContDiff ℝ (⊤ : ℕ∞) (E a j))
    (hper : ∀ (a : Fin A) (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c),
      B a (p.1, p.2 + Pi.single j 1) = B a p ∧ (∀ k, C a k (p.1, p.2 + Pi.single j 1) = C a k p) ∧
        ∀ j', E a j' (p.1, p.2 + Pi.single j 1) = E a j' p)
    (S : Set (Fin r → ℝ)) (hS : IsCompact S)
    (hsupp : ∀ (a : Fin A) (p : (Fin r → ℝ) × (Fin c → ℝ)), p.1 ∉ S →
      B a p = 0 ∧ (∀ k, C a k p = 0) ∧ ∀ j, E a j p = 0)

    (sub : ℕ → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hsub : ∀ i, sub i ≤ Λ)
    (shape : ℕ → Fin A) (lam : ℕ → ℂ) (hlam : Summable fun i => ‖lam i‖)
    (x₀ : ℕ → Fin r → ℝ) (n₀ : ℕ → Fin d → ℤ) (θ₀ : ℕ → Fin c → ℝ) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum r d c, ∀ n : Fin d → ℤ,
      𝒜.coeff n = ∑' i : ℕ, lam i * ∑' γ : sub i,
        if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
          B (shape i) (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) +
            ∑ k : Fin q, ((|1 - Real.exp ((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kR k))| : ℝ) : ℂ) * C (shape i) k (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) +
            ∑ j : Fin c, ((‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
              E (shape i) j (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ)))
        else 0 := by sorry
