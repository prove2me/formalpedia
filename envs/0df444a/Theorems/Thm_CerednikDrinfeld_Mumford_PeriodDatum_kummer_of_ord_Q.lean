-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_kummer_of_ord_Q
-- name    : CerednikDrinfeld.Mumford.PeriodDatum.kummer_of_ord_Q
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/6e1941b1-e6e6-582c-a3d4-cb3bcd4ca611
-- title:
--   Kummer law for p-th roots of Mumford periods
-- statement:
--   Let $E$ and $V$ be finite types, let $D$ be a degeneracy datum on them (maps $a,b\colon E\to V$ and widths $w\colon E\to\mathbb{Z}_{>0}$), and write $Z=$ `ribbonKernel D` for the intersection of the kernels of the two pushforwards $(E\to\mathbb Z)\to(V\to\mathbb Z)$ along $a$ and $b$, and $\operatorname{Gram}=$ `ribbonGram D` for the restriction to $Z$ of the width pairing $(x,z)\mapsto\sum_e w(e)x_ez_e$. Let $K\subseteq L$ be fields and $\operatorname{ord}\colon K^\times\to\mathbb Z$ a homomorphism, and let $P$ be a period datum: a symmetric $\mathbb Z$-bilinear pairing $Q\colon Z\times Z\to K^\times$ with $\operatorname{ord}Q(x,y)=\operatorname{Gram}(x,y)$. Points of the torus are the homomorphisms $Z\to L^\times$, among which sits the $\mathbb Z$-submodule `P.U`, and `P.QL x` is the point attached to $x\in Z$ by the datum. Fix a prime $p$, a primitive $p$-th root of unity $\zeta\in L^\times$, and a map $\chi$ from the $p$-torsion of `P.U` to $\operatorname{Hom}_{\mathbb Z}(Z,\mathbb Z/p)$ such that $v(z)=\zeta^{\chi(v)(z)}$ for all such $v$ and all $z\in Z$. Let $s$ be a ring endomorphism of $L$ fixing $K$ pointwise and fixing $\zeta$; let $\varpi\in K^\times$ have $\operatorname{ord}\varpi=1$; assume every $a\in K^\times$ with $\operatorname{ord}a=0$ is a $p$-th power in $K^\times$; and let $\tau\in\mathbb Z/p$ be such that $s(b)=\zeta^{\tau}b$ for every $b\in L$ with $b^p=\varpi$. Then for every $u\in$ `P.U` and $x\in Z$ with $p\cdot u=$ `P.QL x` there exists $v$ in the $p$-torsion of `P.U` with $s(u(z))=u(z)\,v(z)$ for all $z\in Z$ and $\chi(v)=\tau\cdot(\operatorname{Gram}(x,\cdot)\bmod p)$.
--
--   This is the abstract form of the period law for Mumford uniformisation — the valuation of the multiplicative period pairing is the width (monodromy) pairing — in the shape needed to compute the Kummer cocycle of $s$ on a $p$-th root of a period: the coboundary $s(u)/u$ is the $p$-torsion character $\zeta^{\tau\operatorname{Gram}(x,\cdot)}$, with $\tau$ playing the role of the tame character of $s$. It supplies the Kummer clause of [`CerednikDrinfeld.Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw`](thm.html#CerednikDrinfeld.Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodDatum_kummer_of_ord_Q.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.kummer_of_ord_Q
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)) → (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul (((v : ↥P.U) : P.TorusPoints) z) = ζ ^ (χ v z).val)
    (s : L →+* L) (hsK : ∀ k : K, s (algebraMap K L k) = algebraMap K L k) (hsζ : s ζ = ζ)
    (ϖ : Kˣ) (hϖ : ord (Additive.ofMul ϖ) = 1)
    (hensel : ∀ a : Kˣ, ord (Additive.ofMul a) = 0 → ∃ c : Kˣ, c ^ p = a)
    (τ : ZMod p) (hτ : ∀ b : L, b ^ p = algebraMap K L ϖ → s b = (ζ : L) ^ τ.val * b)
    (u : ↥P.U) (x : ↥(ribbonKernel D)) (hu : (p : ℤ) • (u : P.TorusPoints) = P.QL x) :
    ∃ v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)),
      (∀ z : ↥(ribbonKernel D),
        Additive.ofMul (Units.map (s : L →* L) (Additive.toMul ((u : P.TorusPoints) z))) =
          (u : P.TorusPoints) z + ((v : ↥P.U) : P.TorusPoints) z) ∧
      χ v = τ • ribbonGramModP p D x := by sorry
