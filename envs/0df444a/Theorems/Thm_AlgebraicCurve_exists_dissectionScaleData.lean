-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_dissectionScaleData
-- name    : AlgebraicCurve.exists_dissectionScaleData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/98408338-b4de-5cee-833d-17e362f0e13d
-- title:
--   Scale data for dissecting a compact complex curve
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure. The hypothesis `hfg` asserts the existence of an element of $F$ transcendental over $\mathbb{C}$ over whose adjunction $F$ is finite-dimensional. The instance hypotheses require: `IsCurveOver ℂ F`, i.e. $F$ has principal divisors (for every $f \neq 0$ there is a finitely supported divisor whose value at each place $v$ is $v.\mathrm{ord}\,f = -\log$ of the adic valuation of $f$, of degree $0$), every residue field $v.\mathrm{ResidueField}$ of a place is a finite $\mathbb{C}$-module, and $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$; `HasCanonicalDivisor`, i.e. for every nonzero $\omega \in \Omega[F/\mathbb{C}]$ there is a divisor whose value at each place $v$ is $v.\mathrm{ordDifferential}\,\omega = v.\mathrm{ord}$ of the differential coefficient of $\omega$; and, on the space $\mathrm{Place}\,\mathbb{C}\,F$ of places of $F$ over $\mathbb{C}$ (valuation subrings of $F$, proper, containing the image of $\mathbb{C}$, and principal ideal rings), a topology, a $\mathbb{C}$-charted structure, an analytic manifold structure on the model $\mathbb{C}$, compactness, Hausdorffness and connectedness.
--
--   The hypothesis `hF` is the compatibility of the manifold structure with the valuation-theoretic orders: for every $f \neq 0$ in $F$ and every place $v$, the function $z \mapsto \mathrm{evalAt}$ of $f$ at the place $(\mathrm{extChartAt}\,v)^{-1}(z)$ — where $\mathrm{evalAt}$ is the residue of $f$ read back in $\mathbb{C}$ when $f$ lies in the valuation subring and $0$ otherwise — is meromorphic at the chart image of $v$, with meromorphic order there equal to $v.\mathrm{ord}\,f$.
--
--   Finally a place $P_0$ and a finite set $S$ of places are marked.
--
--   The conclusion asserts the existence of: an element $x \in F$, a natural number $n$, a finite set $\mathrm{Bad} \subseteq \mathbb{C}$, reals $o$ (grid offset) and $hm$ (mesh), integers $jlo, jhi, klo, khi$ delimiting a window of grid squares, a real $Rw$, a partial function $\mathrm{capAt} : \mathbb{Z} \times \mathbb{Z} \to \mathrm{Option}\,\mathbb{C}$, sets $\mathrm{margin}(p) \subseteq \mathbb{C}$ indexed by grid positions, sheets $\mathrm{sheet}(p, i)$ which are open partial homeomorphisms from $\mathrm{Place}\,\mathbb{C}\,F$ to $\mathbb{C}$ indexed by $p \in \mathbb{Z}\times\mathbb{Z}$ and $i \in \mathrm{Fin}\,n$, data $\mathrm{cap}\zeta(b,w)$ (an open partial homeomorphism), $\mathrm{cap}\rho(b,w) \in \mathbb{R}$, $\mathrm{cape}(b,w) \in \mathbb{N}$ indexed by $b \in \mathbb{C}$ and a place $w$, a function $cs : \mathbb{C} \to \mathbb{R}$, data $\inf\zeta(w)$, $\inf\rho(w)$, $\mathrm{infe}(w)$ indexed by a place $w$, and centres $\mathrm{centre} : \mathbb{Z}\times\mathbb{Z} \to \mathbb{C}$, subject to the following conjuncts.
--
--   Structure function: $x$ is transcendental over $\mathbb{C}$; $F$ is finite-dimensional over $\mathbb{C}(x) = \mathbb{C}$ adjoined $x$; $0 < n$; $n$ equals the $\mathbb{C}(x)$-rank of $F$; for every $b \in \mathbb{C}$ the set of places $w$ with $x$ in the valuation subring of $w$ and $\mathrm{evalAt}_w(x) = b$ is finite; for every $t \notin \mathrm{Bad}$ that set has cardinality exactly $n$; and the set of places at which $x$ is not in the valuation subring (the poles of $x$) is finite.
--
--   Grid and window: $0 < hm$; $jlo + 1 < jhi$ and $klo + 1 < khi$; $1 < Rw$; every $z$ with $\|z\| \le Rw$ satisfies $o + jlo\,hm < \mathrm{Re}\,z < o + (jhi+1)hm$ and $o + klo\,hm < \mathrm{Im}\,z < o + (khi+1)hm$; every $z$ with $\|z\| < Rw - 1$ satisfies the same inequalities with the window shrunk by one square on each side, i.e. $o + (jlo+1)hm < \mathrm{Re}\,z < o + jhi\,hm$ and $o + (klo+1)hm < \mathrm{Im}\,z < o + khi\,hm$.
--
--   Branch values against the grid: every $b \in \mathrm{Bad}$ has $\|b\| < Rw - 1$; no $b \in \mathrm{Bad}$ lies on a grid line, i.e. $\mathrm{Re}\,b - o \neq j\,hm$ and $\mathrm{Im}\,b - o \neq j\,hm$ for all $j \in \mathbb{Z}$; distinct $b, b' \in \mathrm{Bad}$ have grid indices differing by at least $2$ in the horizontal or in the vertical coordinate, where the indices are the floors $\lfloor(\mathrm{Re}\,b - o)/hm\rfloor$, $\lfloor(\mathrm{Im}\,b - o)/hm\rfloor$; $\mathrm{capAt}(p) = \mathrm{some}\,b$ holds if and only if $b \in \mathrm{Bad}$ and the two floors of $b$ equal $p_1$ and $p_2$; and $\mathrm{capAt}(p) = \mathrm{none}$ whenever $p_1 \in \{jlo, jhi\}$ or $p_2 \in \{klo, khi\}$, so the outermost ring of the window carries no branch value.
--
--   Margins and sheets over plain squares: for every $p$ in $[jlo, jhi] \times [klo, khi]$ with $\mathrm{capAt}(p) = \mathrm{none}$, the set $\mathrm{margin}(p)$ is open, contains the closed square $\{z : \mathrm{Re}\,z \in [o + p_1 hm, o + (p_1+1)hm],\ \mathrm{Im}\,z \in [o + p_2 hm, o + (p_2+1)hm]\}$, and contains no element of $\mathrm{Bad}$; moreover for such $p$ the $n$ maps $\mathrm{sheet}(p, i)$, $i \in \mathrm{Fin}\,n$, all have target $\mathrm{margin}(p)$, each satisfies on its source that $x$ lies in the valuation subring of each place $P$ there with $\mathrm{sheet}(p,i)(P) = \mathrm{evalAt}_P(x)$, their sources are pairwise disjoint, and every place $P$ with $x$ in its valuation subring and $\mathrm{evalAt}_P(x) \in \mathrm{margin}(p)$ lies in the source of some $\mathrm{sheet}(p,i)$.
--
--   Separation scales at branch values: for every $b \in \mathrm{Bad}$, $4\,hm < cs(b)$, and $2\,cs(b) \le \mathrm{dist}(b, b')$ for every other $b' \in \mathrm{Bad}$.
--
--   Normal charts over branch values: for every $b \in \mathrm{Bad}$ and every place $w$ with $x$ in the valuation subring of $w$ and $\mathrm{evalAt}_w(x) = b$: $0 < \mathrm{cap}\rho(b,w)$, $0 < \mathrm{cape}(b,w)$, $w$ lies in the source of $\mathrm{cap}\zeta(b,w)$ and is sent to $0$, the target of $\mathrm{cap}\zeta(b,w)$ is the ball $B(0, \mathrm{cap}\rho(b,w))$, its source is contained in the source of the extended chart at $w$, the composite $\mathrm{cap}\zeta(b,w) \circ (\mathrm{extChartAt}\,w)^{-1}$ is analytic on a neighbourhood of the chart image of that source and has nowhere vanishing derivative there, every place $P$ in the source satisfies $x - b \in$ the valuation subring of $P$ with $\mathrm{evalAt}_P(x - b) = (\mathrm{cap}\zeta(b,w)(P))^{\mathrm{cape}(b,w)}$, and $\mathrm{cape}(b,w) = (w.\mathrm{ord}(x - b))^{+}$ (the natural-number truncation of the order). Furthermore $2\,cs(b) < \mathrm{cap}\rho(b,w)^{\mathrm{cape}(b,w)}$, so the chart covers the $\mathrm{cape}$-th roots of the disc of radius $2\,cs(b)$; the sources of $\mathrm{cap}\zeta(b,w)$ and $\mathrm{cap}\zeta(b,w')$ are disjoint for distinct places $w \neq w'$ in the fibre of $b$; and every place $P$ with $x$ in its valuation subring and $\|\mathrm{evalAt}_P(x) - b\| < 2\,cs(b)$ lies in the source of $\mathrm{cap}\zeta(b,w)$ for some $w$ in the fibre of $b$.
--
--   Normal charts at the poles: for every place $w$ with $x$ not in the valuation subring of $w$: $0 < \inf\rho(w)$, $0 < \mathrm{infe}(w)$, $w$ lies in the source of $\inf\zeta(w)$ and is sent to $0$, the target is the ball $B(0, \inf\rho(w))$, the source is contained in the source of the extended chart at $w$, the composite $\inf\zeta(w) \circ (\mathrm{extChartAt}\,w)^{-1}$ is analytic on a neighbourhood of the chart image of the source with nowhere vanishing derivative there, every place $P$ in the source satisfies $x^{-1} \in$ the valuation subring of $P$ with $\mathrm{evalAt}_P(x^{-1}) = (\inf\zeta(w)(P))^{\mathrm{infe}(w)}$, and $\mathrm{infe}(w) = (w.\mathrm{ord}\,x^{-1})^{+}$. Furthermore $1/Rw < \inf\rho(w)^{\mathrm{infe}(w)}$; the sources of $\inf\zeta(w)$ and $\inf\zeta(w')$ are disjoint for distinct poles $w \neq w'$; and every place $P$ with $x$ in its valuation subring and $Rw \le \|\mathrm{evalAt}_P(x)\|$ lies in the source of $\inf\zeta(w)$ for some pole $w$.
--
--   Centres: for every $p \in \mathbb{Z}\times\mathbb{Z}$, $\mathrm{centre}(p)$ lies in the open square $o + p_1 hm < \mathrm{Re} < o + (p_1+1)hm$, $o + p_2 hm < \mathrm{Im} < o + (p_2+1)hm$; and if $p_1 = jhi$ and the square straddles the real axis ($o + p_2 hm < 0 < o + (p_2+1)hm$) then $\mathrm{centre}(p)$ has imaginary part $0$.
--
--   Marked places: for every $v$ in $\{P_0\} \cup S$ with $x$ in the valuation subring of $v$ and $\mathrm{evalAt}_v(x) \notin \mathrm{Bad}$: $\|\mathrm{evalAt}_v(x)\| < Rw - 1$, the point $\mathrm{evalAt}_v(x)$ lies on no grid line, the square $p$ given by its two floors has $\mathrm{capAt}(p) = \mathrm{none}$, and $\mathrm{centre}(p) = \mathrm{evalAt}_v(x)$. For $v, v'$ in $\{P_0\} \cup S$ with $x$ in both valuation subrings, both values outside $\mathrm{Bad}$ and $\mathrm{evalAt}_v(x) \neq \mathrm{evalAt}_{v'}(x)$, the corresponding pairs of floors differ. Finally, for every $v$ in $\{P_0\} \cup S$ with $x$ in the valuation subring of $v$, $\|\mathrm{evalAt}_v(x)\| < Rw - 1$.
--
--   This is the combinatorial and analytic input for dissecting a compact Riemann surface, presented here as the space of places of a function field $F$ over $\mathbb{C}$, into cells adapted to a chosen meromorphic function $x$: a square grid in the $x$-plane separating the branch values of $x$, sheets of $x$ over the plain squares, and normal charts $x - b = \zeta^{e}$ at the places over a branch value and $x^{-1} = \zeta^{e}$ at the poles, together with marked-point data for a distinguished place $P_0$ and a finite set $S$. It is used by [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily), which converts this scale data into the cell family of the dissection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_dissectionScaleData.lean

import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open Set AlgebraicCurve Complex

theorem AlgebraicCurve.exists_dissectionScaleData
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
    ∃ (x : F) (n : ℕ) (Bad : Finset ℂ) (o : ℝ) (hm : ℝ) (jlo : ℤ) (jhi : ℤ) (klo : ℤ) (khi : ℤ)
      (Rw : ℝ) (capAt : ℤ × ℤ → Option ℂ) (margin : ℤ × ℤ → Set ℂ)
      (sheet : ℤ × ℤ → Fin n → OpenPartialHomeomorph (Place ℂ F) ℂ)
      (capζ : ℂ → Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ) (capρ : ℂ → Place ℂ F → ℝ)
      (cape : ℂ → Place ℂ F → ℕ) (cs : ℂ → ℝ)
      (infζ : Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ) (infρ : Place ℂ F → ℝ)
      (infe : Place ℂ F → ℕ) (centre : ℤ × ℤ → ℂ),
      (Transcendental ℂ x) ∧
      (FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F) ∧
      (0 < n) ∧
      (n = Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F) ∧
      (∀ b : ℂ, {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}.Finite) ∧
      (∀ t : ℂ, t ∉ Bad →
        {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = t}.ncard = n) ∧
      ({w : Place ℂ F | x ∉ w.toValuationSubring}.Finite) ∧
      (0 < hm) ∧
      (jlo + 1 < jhi) ∧
      (klo + 1 < khi) ∧
      (1 < Rw) ∧
      (∀ z : ℂ, ‖z‖ ≤ Rw →
        (o + jlo * hm < z.re ∧ z.re < o + (jhi + 1) * hm) ∧ (o + klo * hm < z.im ∧ z.im < o + (khi + 1) * hm)) ∧
      (∀ z : ℂ, ‖z‖ < Rw - 1 →
        (o + (jlo + 1) * hm < z.re ∧ z.re < o + jhi * hm) ∧ (o + (klo + 1) * hm < z.im ∧ z.im < o + khi * hm)) ∧
      (∀ b ∈ Bad, ‖b‖ < Rw - 1) ∧
      (∀ b ∈ Bad, ∀ j : ℤ, b.re - o ≠ j * hm ∧ b.im - o ≠ j * hm) ∧
      (∀ b ∈ Bad, ∀ b' ∈ Bad, b ≠ b' →
        2 ≤ |⌊(b.re - o) / hm⌋ - ⌊(b'.re - o) / hm⌋| ∨ 2 ≤ |⌊(b.im - o) / hm⌋ - ⌊(b'.im - o) / hm⌋|) ∧
      (∀ (p : ℤ × ℤ) (b : ℂ), capAt p = some b ↔
        b ∈ Bad ∧ ⌊(b.re - o) / hm⌋ = p.1 ∧ ⌊(b.im - o) / hm⌋ = p.2) ∧
      (∀ p : ℤ × ℤ, p.1 = jlo ∨ p.1 = jhi ∨ p.2 = klo ∨ p.2 = khi → capAt p = none) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → IsOpen (margin p)) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
        {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
          z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ⊆ margin p) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → ∀ b ∈ Bad, b ∉ margin p) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
        ((∀ i, (sheet p i).target = margin p) ∧
            (∀ i, ∀ P ∈ (sheet p i).source, x ∈ P.toValuationSubring ∧ sheet p i P = Place.evalAt P x) ∧
            (Pairwise fun i j => Disjoint (sheet p i).source (sheet p j).source) ∧
            (∀ P : Place ℂ F, x ∈ P.toValuationSubring → Place.evalAt P x ∈ margin p →
              ∃ i, P ∈ (sheet p i).source))) ∧
      (∀ b ∈ Bad, 4 * hm < cs b) ∧
      (∀ b ∈ Bad, ∀ b' ∈ Bad, b' ≠ b → 2 * cs b ≤ dist b b') ∧
      (∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
        (0 < capρ b w ∧ 0 < cape b w ∧ w ∈ (capζ b w).source ∧ capζ b w w = 0 ∧
            (capζ b w).target = Metric.ball 0 (capρ b w) ∧
            (capζ b w).source ⊆ (extChartAt 𝓘(ℂ, ℂ) w).source ∧
            AnalyticOnNhd ℂ (capζ b w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w '' (capζ b w).source) ∧
            (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) w '' (capζ b w).source, deriv (capζ b w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z ≠ 0) ∧
            (∀ P ∈ (capζ b w).source, (x - algebraMap ℂ F b) ∈ P.toValuationSubring ∧ Place.evalAt P (x - algebraMap ℂ F b) = (capζ b w P) ^ cape b w) ∧
            cape b w = (w.ord (x - algebraMap ℂ F b)).toNat)) ∧
      (∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
        2 * cs b < capρ b w ^ cape b w) ∧
      (∀ b ∈ Bad, ∀ w w' : Place ℂ F,
        x ∈ w.toValuationSubring → Place.evalAt w x = b →
        x ∈ w'.toValuationSubring → Place.evalAt w' x = b → w ≠ w' →
        Disjoint (capζ b w).source (capζ b w').source) ∧
      (∀ b ∈ Bad, ∀ P : Place ℂ F, x ∈ P.toValuationSubring →
        ‖Place.evalAt P x - b‖ < 2 * cs b →
        ∃ w : Place ℂ F, x ∈ w.toValuationSubring ∧ Place.evalAt w x = b ∧ P ∈ (capζ b w).source) ∧
      (∀ w : Place ℂ F, x ∉ w.toValuationSubring → (0 < infρ w ∧ 0 < infe w ∧ w ∈ (infζ w).source ∧ infζ w w = 0 ∧
        (infζ w).target = Metric.ball 0 (infρ w) ∧
        (infζ w).source ⊆ (extChartAt 𝓘(ℂ, ℂ) w).source ∧
        AnalyticOnNhd ℂ (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w '' (infζ w).source) ∧
        (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) w '' (infζ w).source, deriv (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z ≠ 0) ∧
        (∀ P ∈ (infζ w).source, x⁻¹ ∈ P.toValuationSubring ∧ Place.evalAt P x⁻¹ = (infζ w P) ^ infe w) ∧
        infe w = (w.ord x⁻¹).toNat)) ∧
      (∀ w : Place ℂ F, x ∉ w.toValuationSubring → 1 / Rw < infρ w ^ infe w) ∧
      (∀ w w' : Place ℂ F, x ∉ w.toValuationSubring → x ∉ w'.toValuationSubring → w ≠ w' →
        Disjoint (infζ w).source (infζ w').source) ∧
      (∀ P : Place ℂ F, x ∈ P.toValuationSubring → Rw ≤ ‖Place.evalAt P x‖ →
        ∃ w : Place ℂ F, x ∉ w.toValuationSubring ∧ P ∈ (infζ w).source) ∧
      (∀ p : ℤ × ℤ, (o + p.1 * hm < (centre p).re ∧ (centre p).re < o + (p.1 + 1) * hm) ∧
        (o + p.2 * hm < (centre p).im ∧ (centre p).im < o + (p.2 + 1) * hm)) ∧
      (∀ p : ℤ × ℤ, p.1 = jhi → o + p.2 * hm < 0 → 0 < o + (p.2 + 1) * hm → (centre p).im = 0) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → Place.evalAt v x ∉ Bad →
        ‖Place.evalAt v x‖ < Rw - 1 ∧
        (∀ j : ℤ, (Place.evalAt v x).re - o ≠ j * hm ∧ (Place.evalAt v x).im - o ≠ j * hm) ∧
        capAt (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = none ∧
        centre (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = Place.evalAt v x) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∀ v' ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → x ∈ v'.toValuationSubring →
        Place.evalAt v x ∉ Bad → Place.evalAt v' x ∉ Bad → Place.evalAt v x ≠ Place.evalAt v' x →
        (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) ≠
          (⌊((Place.evalAt v' x).re - o) / hm⌋, ⌊((Place.evalAt v' x).im - o) / hm⌋)) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → ‖Place.evalAt v x‖ < Rw - 1) := by sorry
