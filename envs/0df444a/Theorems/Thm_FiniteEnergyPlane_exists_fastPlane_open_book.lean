-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_open_book
-- name    : FiniteEnergyPlane.exists_fastPlane_open_book
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:53:11.934582+00:00
-- url     : https://prove2.me/theorems/39f912f9-b1c8-4038-8b6c-75ee39e06c5e
-- title:
--   Open book decompositions with pages projected from fast finite-energy planes
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level (in the sense of `HryniewiczCriterion`), $H$ the same function on $V=\mathbb{R}^{2\cdot(1+1)}$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit of $H$ with $\mu_{CZ}(P)\ge3$. Suppose every periodic Reeb orbit of period at most $T_P$ is nondegenerate, $\gamma>0$ is smaller than every such period and than every difference of two distinct such periods, and $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}(\mathbb{C},\mathbb{R}^4)$ for every compact $K\subset\mathbb{R}^4\setminus\{0\}$ with $K\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset$. If there is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$, then for every $l\ge1$ there is a $C^l$ map $U:\mathbb{R}\times\mathbb{C}\to\mathbb{R}^4$, $1$-periodic in the first variable, such that
--   1. every $U(\theta,\cdot)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$;
--   2. $\mathrm{pageMap}\,H\,U$ avoids $x(\mathbb{R})$, maps $[0,1)\times\mathbb{C}$ bijectively onto $S\setminus x(\mathbb{R})$, has injective derivative, and is Reeb positive (`IsPlaneOpenBook`);
--   3. every Reeb trajectory $y$ with $y(0)\notin x(\mathbb{R})$ meets $\mathrm{proj}(U(\theta,\mathbb{C}))$ at times larger than any given $n$ and at times smaller than any given $n$, for every $\theta\in\mathbb{R}$.
--
--   **Formalization Note** The level is given in the form of `exists_transverse_disk_open_book_of_approx` and of the goal of the previous mission. Periods are those of `ReebOrbit H` (not necessarily minimal, so multiple covers count). The hypothesis on $\Lambda(K,P)$ is exactly the conclusion of `isSeqCompact_embeddedFastPlaneSet` for the same $\gamma$, quantified over $K$; the cylinder $\mathbb{R}\times x(\mathbb{R})$ is the cone $\{y\neq0:\mathrm{proj}(y)\in x(\mathbb{R})\}$. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated. Hryniewicz assumes every contractible orbit nondegenerate; only orbits of period at most $T_P$ appear here. Clause 3, together with transversality of the leaves to the Reeb field (`isFastPlane_immersion_transverse`), is the statement that each page is a global surface of section. The given plane $\tilde u_0$ is a hypothesis only; the theorem does not assert that it is a page, nor does Hryniewicz's Theorem 2.5. See `FiniteEnergyPlane_OpenBook` for "orientation preserving" and the period.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 2.5

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Theorem 2.5, for a strictly star-shaped level `S = H⁻¹(1) ⊂ ℝ⁴` (in
the coordinates of `HryniewiczCriterion`) and a compatible complex structure `J` on `ξ`. Let `P` be
a periodic Reeb orbit of Conley–Zehnder index at least `3` such that every periodic orbit of period
at most `P.T` is nondegenerate; let `0 < γ` be smaller than every such period and every difference
of two distinct such periods, and suppose `Λ(K, P)` is sequentially compact in `C^∞_loc` for every
compact `K ⊂ V 1 \ {0}` disjoint from the cone `ℝ × x(ℝ)`. If there is an embedded fast
finite-energy plane asymptotic to `P` at `∞`, then for every `l ≥ 1` there is a `C^l` map
`U : ℝ × ℂ → V 1`, `1`-periodic in the first variable, such that
(1) every `U(θ, ·)` is an embedded fast finite-energy plane asymptotic to `P` at `∞`;
(2) `pageMap H U` avoids `x(ℝ)`, maps `[0, 1) × ℂ` bijectively onto `S \ x(ℝ)`, has injective
derivative, and is positive against the Reeb field (`IsPlaneOpenBook`);
(3) every Reeb trajectory `y` with `y 0 ∉ x(ℝ)` meets every leaf `pageMap H U (θ, ·)` at times larger
than any given `n` and at times smaller than any given `n`. -/
theorem exists_fastPlane_open_book (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    P.IsCZAtLeast 3 → (∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate) →
    ∀ γ : ℝ, 0 < γ → (∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T) →
    (∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|) →
    (∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ)) →
    ∀ u₀ : ℂ → V 1, IsFastPlane H J u₀ → IsNondegenerateEnd H u₀ cylInf P 1 → IsEmbeddedPlane u₀ →
    ∀ l : ℕ, 1 ≤ l → ∃ U : ℝ × ℂ → V 1, IsPlaneOpenBook H J P l U ∧
      ∀ y : ℝ → V 1, IsReebTrajectory H y → y 0 ∉ Set.range P.x → ∀ θ n : ℝ,
      (∃ t > n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) ∧
      (∃ t < n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) := by
  sorry

end FiniteEnergyPlane
