-- Prove2me | Theorems.Thm_ContactTopology_periodic_legendrian_family_contact_generator
-- name    : ContactTopology.periodic_legendrian_family_contact_generator
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:33:28.466222+00:00
-- url     : https://prove2.me/theorems/af86851a-e0e9-439f-b11f-09eb3de2c601
-- title:
--   Compact equivariant contact generator for a Legendrian neighborhood isotopy
-- statement:
--   Let $H_t$ be a jointly smooth family on the covering coordinates $(x,y,z)\in\mathbb R^3$. Suppose that, for every real time, its restriction to the fixed strip $|y|,|z|<e$ is injective and pulls $dz-y\,dx$ back to a positive multiple of itself. Suppose also that the family commutes with longitudinal translation by one half.
--
--   There is a smaller positive width $d<e$ and a globally smooth time-dependent vector field $X_t$ on $\mathbb R^4$, with one compact spatial support valid for all times, such that $X_t$ is odd and, on the sphere for $0\le t\le1$, tangent and infinitesimally contact:
--   $$\mathcal L_{X_t}\lambda=\mu_t\lambda\quad\text{on }TS^3.$$
--   Here $\mu$ is jointly smooth. Throughout the entire smaller moving tube, the field agrees exactly with the prescribed local velocity:
--   $$X_t\bigl(\chi(H_t(p))\bigr)=\partial_t\bigl(\chi(H_t(p))\bigr)\qquad(|p_y|,|p_z|\le d).$$
--
--   The explicit contact cover $\chi$ is radial normalization of the four-vector displayed in the formal statement; longitudinal half-translation is its antipodal action. This is the infinitesimal extension step used to extend a local Legendrian-neighborhood contact isotopy by a compact contact Hamiltonian. Integration and the resulting ambient contact isotopy are separate conclusions.
-- source:
--   Derived local contact-isotopy extension generator: Geiges, Contact geometry, arXiv:math/0307242v2, Theorem 2.42 and proof, printed pp. 34–36; https://arxiv.org/abs/math/0307242 . Legendrian-neighborhood application: Min, arXiv:2207.03590v2, Lemma 2.7(2), printed pp. 10–12. The explicit sphere cover, parameterized inverse charts, radial descent, invariant first-jet extension, and exact generator matching are supplied here; this is a derived supporting theorem, not a verbatim numbered statement.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open scoped ContDiff

theorem ContactTopology.periodic_legendrian_family_contact_generator (e : ℝ) (he : 0 < e) (H : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hH : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => H q.1 q.2))
    (hinj : ∀ t, Set.InjOn (H t) {p | |p 1| < e ∧ |p 2| < e})
    (hhalf : ∀ t p, H t (p+![1/2,0,0]) = H t p+![1/2,0,0])
    (hcontact : ∀ t p, |p 1| < e ∧ |p 2| < e → ∃ a : ℝ, 0 < a ∧ ∀ v : Fin 3 → ℝ,
      (fderiv ℝ (H t) p v) 2-(H t p) 1*(fderiv ℝ (H t) p v) 0 = a*(v 2-p 1*v 0)) :
    let chart : (Fin 3 → ℝ) → BirkhoffGlobalSection.Phase := fun p =>
      BirkhoffGlobalSection.radialNormalize
        ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]
    ∃ d : ℝ, 0 < d ∧ d < e ∧
    ∃ X : ℝ → BirkhoffGlobalSection.Phase → BirkhoffGlobalSection.Phase,
    ∃ mu : ℝ → BirkhoffGlobalSection.Phase → ℝ,
      ContDiff ℝ ∞ (fun q : ℝ × BirkhoffGlobalSection.Phase => X q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × BirkhoffGlobalSection.Phase => mu q.1 q.2) ∧
      (∃ C : Set BirkhoffGlobalSection.Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) ∧
      (∀ t y, X t (-y) = -X t y) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ BirkhoffGlobalSection.unitThreeSphere,
        BirkhoffGlobalSection.phaseDot y (X t y) = 0) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ BirkhoffGlobalSection.unitThreeSphere,
        ∀ v : BirkhoffGlobalSection.Phase, BirkhoffGlobalSection.phaseDot y v = 0 →
          BirkhoffGlobalSection.phaseRadialContact (X t y) v+
            BirkhoffGlobalSection.phaseRadialContact y (fderiv ℝ (X t) y v) =
            mu t y*BirkhoffGlobalSection.phaseRadialContact y v) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ p : Fin 3 → ℝ, |p 1| ≤ d → |p 2| ≤ d →
        X t (chart (H t p)) = fderiv ℝ (fun q : ℝ × (Fin 3 → ℝ) => chart (H q.1 q.2)) (t,p) (1,0) := by sorry
