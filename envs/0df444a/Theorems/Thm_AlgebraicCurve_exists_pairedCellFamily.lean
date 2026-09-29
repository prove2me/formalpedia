-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_pairedCellFamily
-- name    : AlgebraicCurve.exists_pairedCellFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/68cdab62-b41b-53fa-bf6d-4ed32fd87b3b
-- title:
--   Existence of a paired cell family on a compact complex curve
-- statement:
--   Let $F$ be a field that is a $\mathbb{C}$-algebra, assumed to contain an element $x$ transcendental over $\mathbb{C}$ with $F$ finite-dimensional over $\mathbb{C}(x)$, to satisfy `IsCurveOver ℂ F` (principal divisors, finite residue extensions, $\Omega[F/\mathbb{C}]$ free of rank $1$) and `HasCanonicalDivisor` (every nonzero Kähler differential has a divisor whose value at each place $v$ is $v$'s differential order), and whose place space $\mathrm{Place}\,\mathbb{C}\,F$ carries a compact, Hausdorff, connected analytic $\mathbb{C}$-manifold structure; assume further that for every $f \neq 0$ and every place $v$ the function $z \mapsto \mathrm{evalAt}_{\zeta^{-1}(z)}(f)$, read in the extended chart at $v$, is meromorphic at $v$ with meromorphic order $v.\mathrm{ord}\,f$. Given a place $P_0$ and a finite set $S$ of places, there exist $m$ and cells $\mathrm{cell}\,C$ ($C \in \mathrm{Fin}\,m$), each an analytic coordinate $\zeta$ together with a radial region $R$ whose closed region lies in $\zeta$'s target, a map $\mathrm{pair}$ on the set of all pairs $(C,k)$ with $k < N_C$ and a Boolean $\mathrm{orient}$, such that: $\mathrm{pair}$ is an involution and $\mathrm{orient}$ is negated by it (so $\mathrm{pair}$ is fixed-point free); whenever $\mathrm{pair}\,(C,k) = (C',k')$ with $\mathrm{orient}\,(C,k)$ true, there is $\psi : \mathbb{R} \to \mathbb{R}$, strictly decreasing and $C^1$ on the parameter interval $[\varphi_{k'},\varphi_{k'+1}]$ of $C'$, exchanging its endpoints with $\varphi_{k+1},\varphi_{k}$ respectively, with $\mathrm{bdry}_{C'}(t) = \mathrm{bdry}_{C}(\psi\,t)$ throughout; the carriers $\zeta^{-1}(R.K)$ cover all places; any two cells whose carriers contain a common place $x$ are joined by a chain of cells consecutively sharing a paired arc through $x$; each place of $\{P_0\} \cup S$ lies in some cell's interior $\zeta^{-1}(R.\mathrm{Kint})$; each carrier meets $S$ in at most one point; the arc endpoint places $v = \mathrm{bdry}_C(\varphi_k)$ or $\mathrm{bdry}_C(\varphi_{k+1})$ number $V$ with $2V - \sum_C N_C + 2m = 2(2 - 2g)$, where $g = \dim_{\mathbb{C}} \mathrm{regularDifferentials}\,\mathbb{C}\,F$; and each $v \in S$ lies in the interior of a cell with $\zeta(v) = R.q$, the centre of its radial region.
--
--   This is the cell-dissection (triangulation-type) statement for a compact connected complex curve presented as the place space of a function field: finitely many analytically coordinatised radial cells cover the curve, their boundary arcs are matched in orientation-reversing pairs by a reparametrisation, the marked points of $S$ are separated and centred, and the resulting vertex–edge–face count realises the Euler characteristic $2 - 2g$ with $g$ the dimension of the space of regular differentials. It is the grid-construction helper feeding [`AlgebraicCurve.exists_cellDissection`](thm.html#AlgebraicCurve.exists_cellDissection).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_pairedCellFamily.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open Set AlgebraicCurve Complex

theorem AlgebraicCurve.exists_pairedCellFamily
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (m : ℕ) (cell : Fin m → Cell F)
      (pair : (Σ C : Fin m, Fin (cell C).R.N) → (Σ C : Fin m, Fin (cell C).R.N))
      (orient : (Σ C : Fin m, Fin (cell C).R.N) → Bool),
      (∀ a, pair (pair a) = a) ∧
      (∀ a, orient (pair a) = !orient a) ∧
      (∀ (C : Fin m) (k : Fin (cell C).R.N) (C' : Fin m)
        (k' : Fin (cell C').R.N),
        pair ⟨C, k⟩ = ⟨C', k'⟩ → orient ⟨C, k⟩ = true →
        ∃ ψ : ℝ → ℝ,
          StrictAntiOn ψ ((cell C').R.arcIcc k') ∧
          ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
          ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
          ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
          ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)) ∧
      (∀ w : Place ℂ F, ∃ C : Fin m, w ∈ (cell C).carrier) ∧
      (∀ (C C' : Fin m) (x : Place ℂ F), x ∈ (cell C).carrier →
        x ∈ (cell C').carrier → Relation.ReflTransGen
          (fun X Y : Fin m => ∃ (k : Fin (cell X).R.N) (k' : Fin (cell Y).R.N),
            pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (cell X).arc k) C C') ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : Fin m, v ∈ (cell C).interior') ∧
      (∀ C : Fin m, ((cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      (2 * ({v : Place ℂ F | ∃ (C : Fin m) (k : Fin (cell C).R.N),
        v = (cell C).bdry ((cell C).R.φs k.castSucc) ∨
          v = (cell C).bdry ((cell C).R.φs k.succ)}.ncard : ℤ)
        - (∑ C : Fin m, ((cell C).R.N : ℤ)) + 2 * (m : ℤ)
        = 2 * (2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ))) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : Fin m,
        v ∈ (cell C).interior' ∧ (cell C).ζ v = (cell C).R.q) := by sorry
