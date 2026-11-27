-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_Supplement_lemma_5_1
-- name    : ChenWhitt93.Reflection.Supplement.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:55:32.825639+00:00
-- url     : https://prove2.me/theorems/3301807f-a796-4d31-94fb-279968d7076b
-- title:
--   Lemma 5.1 — fluid limit of the busy time with fixed up and down times: Bⁿ(nt)/n → νt
-- statement:
--   Consider a sequence of open networks with $J$ stations, a common routing, arrival rates $\lambda^n$, service rates $\mu^n$, up fractions $\nu^n$ and routing matrix $P$, and let $(Z^n,B^n)$ be the queue-length and busy-time processes of network $n$. Assume, for a fixed sample path (after a Skorohod representation):
--
--   1. every network satisfies the model of Section 3;
--   2. (4.6) $\sqrt n(\lambda^n-\lambda)\to c_\lambda$ with $\lambda\ge0$, (4.7) $\sqrt n(\mu^n-\mu)\to c_\mu$ with $\mu>0$, (5.2) $\sqrt n(\nu^n-\nu)\to c_\nu$ with $0\le\nu\le1$, and the balance condition (5.10) $\lambda_j+\sum_kP_{kj}\mu_k\nu_k=\mu_j\nu_j$; $P$ is substochastic with $P^k\to0$;
--   3. the scaled primitives of (4.1)–(4.4) and (5.1) converge uniformly on compact sets to limits $\hat Z(0)$, $\hat A$, $\hat S$, $\hat R$, $\hat D$, the last four continuous.
--
--   Then
--   $$
--   \frac{B^n(nt)}{n}\ \to\ \nu t\qquad\text{uniformly on compact subsets of }[0,\infty),\ \text{jointly in }\mathbb R^J.
--   $$
--
--   This is the fluid limit of the busy time used in the proof of Theorem 5.2, as Lemma 4.2 is used in the proof of Theorem 4.1.
--
--   **Formalization Note** Uniform convergence on compacts to the continuous path $\nu t$ is convergence in $D([0,\infty),\mathbb R^J,J_1)$.
--
--   Differences from the source:
--   - reading: Bⁿ(nt)/n → νt w.p.1 in D([0, ∞), ℝᴶ, J₁) → for deterministic sequences satisfying the u.o.c. forms of (4.1)–(4.4), (5.1), with (4.6), (4.7), (5.2), (5.10) and Section 3's model, every solution (Zⁿ, Bⁿ) has n⁻¹Bⁿ(nt) → νt u.o.c.; reason: 'w.p.1' refers to the Skorohod-represented versions of the proof of Theorem 4.1 (p. 351); the proof of Lemma 5.1 (p. 357) argues path by path, as the published lemma_4_2 does; J₁ convergence to the continuous νt is u.o.c.
--   - generalization: a network of J stations → J : ℕ also permits the empty network J = 0; reason: for J > 0 the full source claim is unchanged; for J = 0 all station vectors are empty and each convergence conclusion is immediate
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 356, Lemma 5.1 (proof p. 357, (5.14))

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Supplement_FixedUpDown

namespace ChenWhitt93.Reflection.Supplement

open MeasureTheory Filter Topology Matrix
open ChenWhitt93.JumpDiffusion

/-- Lemma 5.1 (p. 356), in the pathwise (Skorohod-represented) form of its proof: under the
deterministic versions of the assumptions of Section 5 — Section 3's model for every network,
(4.6), (4.7), (5.2), (5.10), `P` substochastic with `Pᵏ → 0`, (4.1)–(4.4) and (5.1) holding
uniformly on compacts with continuous limits — every queue-length / busy-time solution
`(Zⁿ, Bⁿ)` satisfies `n⁻¹ Bⁿ(nt) → νt` uniformly on compact subsets of `[0, ∞)`, jointly in
`ℝᴶ`. -/
theorem lemma_5_1 {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun nun : ℕ → Fin J → ℝ) (lam mu nu clam cmu cnu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (L : LimitData5 J)
    (Z : ℕ → ℝ → Fin J → ℤ) (B : ℕ → ℝ → Fin J → ℝ)
    (hH : PathwiseHyp5 χ net lamn mun nun lam mu nu clam cmu cnu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n)) :
    UocTendsto (fun (n : ℕ) (t : ℝ) (j : Fin J) => B n (n * t) j / n)
      (fun t j => nu j * t) := by sorry

end ChenWhitt93.Reflection.Supplement
