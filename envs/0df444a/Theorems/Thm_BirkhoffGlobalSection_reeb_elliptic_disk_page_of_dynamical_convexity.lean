-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_reeb_elliptic_disk_page_of_dynamical_convexity
-- name    : BirkhoffGlobalSection.reeb_elliptic_disk_page_of_dynamical_convexity
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T03:41:55.715242+00:00
-- url     : https://prove2.me/theorems/3676ef3f-ed21-4f89-9f6f-5a7bab07374f
-- title:
--   Rational disk pages for the radial Reeb flow on a symmetric convex boundary
-- statement:
--   Let $B \subset \mathbb{R}^4$ be a compact convex body with $0$ in its interior and centrally symmetric boundary $S = \partial B$. Let $H$ be smooth near $S$, with $H = 0$, $dH \ne 0$ and positive tangential Hessian on $S$. Assume the radial contact form $\lambda_y(v) = -\tfrac12\,\omega(y,v)$ satisfies $\lambda(X_H) > 0$ on $S$, and that the Hamiltonian flow of $H$ on $S$ is dynamically convex (`IsDynamicallyConvexOn`).
--
--   Let $\psi$ be a complete flow on $S$ with velocity
--   $$
--   R = \frac{X_H}{\lambda(X_H)},
--   $$
--   the Reeb vector field of $\lambda|_S$. Let $\Gamma$ be a simple periodic orbit of $\psi$ with trace $K$, and assume the radial normalization of $K$ bounds a positive elliptic rational disk on the round sphere. Then there is a map $P$ from the closed unit disk to $S$ with the following properties:
--   - $P$ is smooth and an injective immersion on the closed disk;
--   - the interior of $P$ is transverse to $R$;
--   - $P(\partial\mathbb{D}) = K$;
--   - $P(u) = -P(v)$ exactly when $u, v$ are opposite boundary points, $v = -u$;
--   - every $\psi$-trajectory off $K$ meets $P(\operatorname{int}\mathbb{D}) \cup -P(\operatorname{int}\mathbb{D})$ at arbitrarily large positive and arbitrarily large negative times.
--
--   This is the Hryniewicz–Salomão rational open book theorem (Corollary 1.8 with $p = 2$) in the lifted picture.
--   - $S$ and $\lambda$ are invariant under $y \mapsto -y$, so $R(-y) = -R(y)$ even when $H$ is not even. Hence $\psi$ descends to the Reeb flow of a contact form on $S/\{\pm1\} \cong \mathbb{RP}^3$. Radial projection identifies $(S, \ker\lambda)$ with the standard tight sphere, conformally.
--   - Closed orbits on $S$ are the lifts of contractible orbits of the quotient, and the Conley–Zehnder index does not depend on the time parametrization. So the hypothesis is dynamical convexity of the quotient.
--   - The disk hypothesis projects to a $2$-disk for $K/\{\pm1\}$ with embedded interior. Its characteristic foliation has a single positive elliptic singularity, so $K/\{\pm1\}$ is a $2$-unknot with self-linking number $-1/2$.
--   - The theorem then gives a rational open book with binding $K/\{\pm1\}$ whose disk-like pages are global surfaces of section. A page lifts to an embedded disk in $S$ with boundary $K$; its antipodal image is the other lift. Normalizing the boundary parametrization makes antipodal boundary points have opposite parameters.
--
--   **Formalization Note.** The flow is the Reeb flow of $\lambda|_S$, as in the source; $H$ need not be even. Dynamical convexity and $\lambda(X_H) > 0$ are kept as explicit hypotheses. Both follow from strict convexity: the first by Hofer–Wysocki–Zehnder, the second from convexity with positive tangential Hessian.
-- source:
--   Hryniewicz--Salomao, Elliptic bindings for dynamically convex Reeb flows on the real projective three-space, Calc. Var. PDE 55 (2016), https://arxiv.org/html/1505.02713v3, Corollary 1.8 (via Theorem 1.7) with p = 2, and Section 4; author correction https://www.mathga.rwth-aachen.de/~hryniewicz/files/elliptic_errata.pdf (results unaffected; explains how Corollary 1.8 follows from Theorem 1.7). Lifted to the centrally symmetric hypersurface as in Liu--Salomao, https://arxiv.org/html/2506.17867v2, Section 10.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk

open scoped ContDiff

namespace BirkhoffGlobalSection

theorem reeb_elliptic_disk_page_of_dynamical_convexity
    (B : Set Phase) (hBcompact : IsCompact B) (hBconvex : Convex ℝ B)
    (hB0 : (0 : Phase) ∈ interior B)
    (hsymmetric : ∀ y ∈ frontier B, -y ∈ frontier B)
    (H : Phase → ℝ) (hHsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ H y)
    (hHzero : ∀ y ∈ frontier B, H y = 0)
    (hHregular : ∀ y ∈ frontier B, fderiv ℝ H y ≠ 0)
    (hHessian : HasPositiveTangentialHessianOn H (frontier B))
    (hcontact : ∀ y ∈ frontier B,
      0 < phaseRadialContact y (hamiltonianVectorField H y))
    (hdc : IsDynamicallyConvexOn H (frontier B))
    (ψ : Flow ℝ {y : Phase // y ∈ frontier B})
    (hψ : ∀ s t, HasDerivAt (fun v => ((ψ v s : {y : Phase // y ∈ frontier B}) : Phase))
      ((phaseRadialContact (ψ t s) (hamiltonianVectorField H (ψ t s)))⁻¹ •
        hamiltonianVectorField H (ψ t s)) t)
    (Γ : PeriodicOrbit ψ) (hsimple : IsSimplePeriodicOrbit ψ Γ)
    (disk : PositiveEllipticRationalDisk (radialNormalize ''
      Set.range (fun t : ℝ => ((ψ t Γ.point : {y : Phase // y ∈ frontier B}) : Phase)))) :
    ∃ page : Plane → Phase,
      (∀ u ∈ closedUnitDisk, page u ∈ frontier B) ∧
      (∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ page u) ∧
      Set.InjOn page closedUnitDisk ∧
      (∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ page u)) ∧
      (∀ u ∈ openUnitDisk,
        (phaseRadialContact (page u) (hamiltonianVectorField H (page u)))⁻¹ •
            hamiltonianVectorField H (page u) ∉ Set.range (fderiv ℝ page u)) ∧
      page '' unitCircle =
        Set.range (fun t : ℝ => ((ψ t Γ.point : {y : Phase // y ∈ frontier B}) : Phase)) ∧
      (∀ u ∈ closedUnitDisk, ∀ v ∈ closedUnitDisk,
        (page u = -page v ↔ u ∈ unitCircle ∧ v ∈ unitCircle ∧ v = -u)) ∧
      (∀ y : {y : Phase // y ∈ frontier B},
        (y : Phase) ∉ Set.range
          (fun t : ℝ => ((ψ t Γ.point : {y : Phase // y ∈ frontier B}) : Phase)) →
        (∀ R : ℝ, ∃ t : ℝ, R < t ∧ ∃ u ∈ openUnitDisk,
          ((ψ t y : {y : Phase // y ∈ frontier B}) : Phase) = page u ∨
          ((ψ t y : {y : Phase // y ∈ frontier B}) : Phase) = -page u) ∧
        (∀ R : ℝ, ∃ t : ℝ, t < R ∧ ∃ u ∈ openUnitDisk,
          ((ψ t y : {y : Phase // y ∈ frontier B}) : Phase) = page u ∨
          ((ψ t y : {y : Phase // y ∈ frontier B}) : Phase) = -page u)) := by sorry

end BirkhoffGlobalSection
