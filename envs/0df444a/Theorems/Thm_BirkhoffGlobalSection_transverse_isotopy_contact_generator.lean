-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_transverse_isotopy_contact_generator
-- name    : BirkhoffGlobalSection.transverse_isotopy_contact_generator
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T13:33:17.448977+00:00
-- url     : https://prove2.me/theorems/127b6bf7-3a22-4600-82ae-2c5c3205a1bb
-- title:
--   A contact vector field generating an equivariant transverse Hopf isotopy
-- statement:
--   Let $I$ be an equivariant transverse Hopf isotopy $k_t(u) = I(t,u)$, $t \in [0,1]$, of positively transverse knots on the round sphere $S^3 \subset \mathbb{R}^4$, for the radial contact form $\lambda_y(v) = -\tfrac12\,\omega(y,v)$. Then there are smooth functions $X : \mathbb{R}\times\mathbb{R}^4 \to \mathbb{R}^4$ and $\mu : \mathbb{R}\times\mathbb{R}^4 \to \mathbb{R}$ with the following properties.
--   - $X_t$ vanishes outside one fixed compact set for every $t$, and it is odd: $X_t(-y) = -X_t(y)$.
--   - For $t \in [0,1]$, $X_t$ is tangent to $S^3$ and is an infinitesimal automorphism of the contact structure:
--   $$
--   (\mathcal L_{X_t}\lambda)_y(v) = \lambda_{X_t(y)}(v) + \lambda_y\bigl(DX_t(y)\,v\bigr) = \mu_t(y)\,\lambda_y(v) \qquad (y \in S^3,\ v \in T_yS^3).
--   $$
--   - Along the moving knot, $X_t$ is the velocity of the isotopy:
--   $$
--   X_t\bigl(k_t(u)\bigr) = \partial_t k_t(u) \qquad (t \in [0,1],\ u \in S^1).
--   $$
--
--   This is the vector field built in the proof of the isotopy extension theorem for contact submanifolds; transverse knots are one-dimensional contact submanifolds.
--   - Extend $k_t$ to a smooth family of contact embeddings of a tubular neighbourhood, and let $X_t$ be its velocity along the image. This is an infinitesimal automorphism of $\ker\lambda$.
--   - Let $H_t = \lambda(X_t)$ be its contact Hamiltonian. Cut $H_t$ off with a bump function equal to $1$ near the knot. The Hamiltonian field of the cut-off function is compactly supported and smooth in $t$, and it agrees with the velocity along the knot.
--   - The isotopy is smooth near $[0,1]\times S^1$, so the construction runs on a slightly larger time interval and can be cut off in time outside it.
--   - $\lambda$ is invariant under $y \mapsto -y$ and the velocity is odd ($k_t(-u) = -k_t(u)$). So the average $\tfrac12\bigl(X_t(y) - X_t(-y)\bigr)$ keeps every property, with $\mu$ averaged in the same way.
--
--   **Formalization Note.** The Lie derivative is the coordinate formula of `GrayStability.lieDerivOneForm`, $(\mathcal L_X\eta)_y(v) = D\eta_y(X(y))(v) + \eta_y(DX(y)v)$, written out for the form $\lambda$, which is linear in $y$. The velocity is `fderiv ℝ I.isotopy (t, u) (1, 0)`. Integrating $X$ to a contactomorphism is not part of this statement.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242: proof of Theorem 2.42 (isotopy extension for contact submanifolds), pp. 34-36, the vector field X_t with X_t o phi_t o varphi_t = d/dt(phi_t o varphi_t) and its cut-off contact Hamiltonian; Theorem 2.22 (contact Hamiltonians, L_X alpha = dH(R) alpha), p. 16; neighbourhood model of a transverse knot as a one-dimensional contact submanifold, after Theorem 2.32, p. 25. Antipodal averaging of the field for the radial contact form on S^3.

import Definitions.Def_BirkhoffGlobalSection_SphereContact

open scoped ContDiff

namespace BirkhoffGlobalSection

theorem transverse_isotopy_contact_generator (K : Set Phase)
    (I : EquivariantTransverseHopfIsotopy K) :
    ∃ X : ℝ → Phase → Phase, ∃ μ : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => μ p.1 p.2) ∧
      (∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) ∧
      (∀ t y, X t (-y) = -X t y) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        phaseRadialContact (X t y) v + phaseRadialContact y (fderiv ℝ (X t) y v) =
          μ t y * phaseRadialContact y v) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
        X t (I.isotopy (t, u)) = fderiv ℝ I.isotopy (t, u) (1, 0)) := by sorry

end BirkhoffGlobalSection
