-- Prove2me | Theorems.Thm_DiazModulus_interpolation_det_order
-- name    : DiazModulus.interpolation_det_order
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:30.154988+00:00
-- url     : https://prove2.me/theorems/ffb77b9a-aa9e-479d-9430-515df7bded64
-- title:
--   DALAG Lemma 9.2: $\det(D^{\sigma_\mu} f_l(z\zeta_\mu))$ vanishes at $z = 0$ to order at least $\Theta_n(L) - \sum_\mu \sigma_\mu$
-- statement:
--   Let $f_1, \dots, f_L$ be entire functions on $\mathbb{C}^n$, and for $\mu = 1, \dots, L$ let $\zeta_\mu \in \mathbb{C}^n$, $\sigma_\mu \in \mathbb{N}$ and $v_\mu \in (\mathbb{C}^n)^{\sigma_\mu}$. Then $\Delta(z) = \det(D^{\sigma_\mu} f_l(z\zeta_\mu)(v_\mu))_{l,\mu}$ vanishes at $z = 0$ to order at least $\Theta_n(L) - \sum_\mu \sigma_\mu$; precisely, $\Theta_n(L) \leq \mathrm{ord}_0 \Delta + \sum_\mu \sigma_\mu$ in $\mathbb{N} \cup \{\infty\}$. Here $\Theta_n(L)$ is the least value of $\sum_l |\kappa'(l)|$ over the injective maps $\kappa' : \{1, \dots, L\} \to \mathbb{N}^n$, with $|\cdot|$ the total degree of a multi-index ($0$ if there is no such map).
--
--   **Proof.** $\Delta$ is entire, so it suffices that $\Delta^{(j)}(0) = 0$ when $j + \sum_\mu \sigma_\mu < \Theta_n(L)$. By the Leibniz rule for determinants (`DiazModulus.iteratedDeriv_det_eq_sum`) $\Delta^{(j)}(0)$ is a combination of determinants whose column $\mu$ is differentiated $q_\mu$ times, $\sum q_\mu = j$, and by `DiazModulus.iteratedDeriv_iteratedFDeriv_line` each entry is $D^{m_\mu} f_l(0)$ at a tuple of vectors, with $m_\mu = \sigma_\mu + q_\mu$ and $\sum m_\mu < \Theta_n(L)$. Expanding the vectors in the standard basis and using multilinearity, the determinant is a sum of determinants indexed by choices of basis vectors; for each choice let $\kappa'(\mu)$ count how often each basis vector occurs in column $\mu$, a multi-index of degree $m_\mu$. If $\kappa'$ is injective then $\Theta_n(L) \leq \sum m_\mu$, which is excluded; otherwise two columns are equal, by the symmetry of iterated derivatives, and the determinant vanishes.
--
--   **Novelty.** Classical; routine formalisation. This is DALAG Lemma 9.2.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 9.2. Uses DiazModulus.iteratedDeriv_det_eq_sum and DiazModulus.iteratedDeriv_iteratedFDeriv_line. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem interpolation_det_order {n L : ℕ} (f : Fin L → (Fin n → ℂ) → ℂ)
    (hf : ∀ l, AnalyticOnNhd ℂ (f l) Set.univ) (ζ : Fin L → Fin n → ℂ) (σ : Fin L → ℕ)
    (v : (μ : Fin L) → Fin (σ μ) → Fin n → ℂ) :
    ((sInf {S | ∃ κ' : Fin (L) → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun z : ℂ =>
        (Matrix.of fun l μ => iteratedFDeriv ℂ (σ μ) (f l) (z • ζ μ) (v μ)).det) 0
        + ∑ μ, (σ μ : ℕ∞) := by
  sorry

end DiazModulus
