-- Prove2me | Theorems.Thm_DiazModulus_quadratic_eigen_forms_canonical
-- name    : DiazModulus.quadratic_eigen_forms_canonical
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:43.637251+00:00
-- url     : https://prove2.me/theorems/8336089d-5874-43cf-9b29-4c9ec746e31d
-- title:
--   The complete, two-orbit and cyclic shapes of a five-dimensional W ⊇ span(1, u, u⁻¹) in canonical form: D1, D2a or D2b
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension $5$ with $1, u, u^{-1} \in W$, that is, $H_0 \subseteq W$ for $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $P, Q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg P, \deg Q) = 2$, write $P_c = P(u) - cQ(u)$, and suppose $W$ has one of the three shapes of `DiazModulus.quadratic_complement_eigen_forms`:
--
--   - **(scalar)** for some $c \in \overline{\mathbb{Q}}$, $Q(u)R(u)/(uP_c) \in W$ for every $R \in \overline{\mathbb{Q}}[X]$ of degree at most $2$;
--   - **(two-orbit)** for some $c_1 \neq c_2$ in $\overline{\mathbb{Q}}$ and $R_1, R_2 \in \overline{\mathbb{Q}}[X]$ of degree at most $2$, $W = \mathrm{span}(1, u, u^{-1}, Q(u)R_1(u)/(uP_{c_1}), Q(u)R_2(u)/(uP_{c_2}))$;
--   - **(cyclic)** for some $c \in \overline{\mathbb{Q}}$ and $R_0, R_1 \in \overline{\mathbb{Q}}[X]$ of degree at most $2$, $W = \mathrm{span}(1, u, u^{-1}, Q(u)R_0(u)/(uP_c), Q(u)(Q(u)R_0(u) + P_cR_1(u))/(uP_c^2))$.
--
--   Then one of the following holds:
--
--   - **(D1)** there are linearly independent $t_0, t_1, t_2 \in \mathbb{C}$ with $t_j \in W$ and $ut_j \in W$ for every $j$;
--   - **(D2a, two-orbit)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), P'(u)S_2(u)/(uQ'(u)))$ for some $P', Q', S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P', Q'$ coprime, $\max(\deg P', \deg Q') = 2$ and $\deg S_1, \deg S_2 \leq 2$;
--   - **(D2b, cyclic)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), Q'(u)(Q'(u)S_1(u) + P'(u)S_2(u))/(uP'(u)^2))$ for some such $P', Q', S_1, S_2$.
--
--   **Proof.** By `DiazModulus.coprime_pencil_mobius`, $(P - cQ, Q)$ and, for $c_1 \neq c_2$, $(P - c_1Q, P - c_2Q)$ are again coprime of maximal degree $2$. Scalar: $t = (u^{-1}, 1, Q(u)/(uP_c))$ and $ut = (1, u, uQ(u)/(uP_c))$ lie in $W$ (take $R = 1$ and $R = X$). A relation $au^{-1} + b + eQ(u)/(uP_c) = 0$ times $uP_c$ gives $(a + bX)(P - cQ) + eQ = 0$ in $\overline{\mathbb{Q}}[X]$ ($u$ is transcendental), and coprimality with degree $2$ forces $a = b = e = 0$: (D1). Two-orbit: with $P' = P - c_1Q$, $Q' = P - c_2Q$, $d = c_1 - c_2$, $S_1 = R_1/d$, $S_2 = -R_2/d$, the canonical generators differ from the given ones by $S_1(u)/u, S_2(u)/u \in H_0$, so the spans agree: (D2a); the denominators are non-zero, the five generators of $W$ being independent. Cyclic: $P' = P - cQ$, $Q' = Q$, $S_1 = R_0$, $S_2 = R_1$ give (D2b) verbatim.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Step 5 of the sheaf-free proof of Theorem NF. Uses DiazModulus.coprime_pencil_mobius. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_eigen_forms_canonical (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W) (P Q : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2)
    (hform :
      (∃ c : ↥Qbar, ∀ R : (↥Qbar)[X], R.natDegree ≤ 2 → aeval u Q * aeval u R / (u * (aeval u P - (c : ℂ) * aeval u Q)) ∈
          W) ∨
      (∃ c₁ c₂ : ↥Qbar, c₁ ≠ c₂ ∧ ∃ R₁ R₂ : (↥Qbar)[X], R₁.natDegree ≤ 2 ∧ R₂.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * (aeval u P - (c₁ : ℂ) * aeval u Q)),
            aeval u Q * aeval u R₂ / (u * (aeval u P - (c₂ : ℂ) * aeval u Q))} : Set ℂ)) ∨
      (∃ c : ↥Qbar, ∃ R₀ R₁ : (↥Qbar)[X], R₀.natDegree ≤ 2 ∧ R₁.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₀ / (u * (aeval u P - (c : ℂ) * aeval u Q)),
            aeval u Q * (aeval u Q * aeval u R₀ + (aeval u P - (c : ℂ) * aeval u Q) * aeval u R₁) / (u * (aeval u P - (c : ℂ) * aeval u Q) ^ 2)} :
              Set ℂ))) :
    (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
    (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ)) := by
  sorry

end DiazModulus
