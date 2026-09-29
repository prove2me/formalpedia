-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/6cb51e77-336e-5396-920b-b7fef2123c7f
-- title:
--   The r-power exponents of the endomorphism dictionary form a character mod n
-- statement:
--   Fix a prime $r$, rationals $a,b,a_1,b_1$, and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is an order (contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated) and contains every integer scalar; fix $N$ and a nonzero $n$ with $r\nmid n$, a nontrivial commutative ring $k_0$, a field $K_0$ of characteristic $0$, and a map $\mathrm{coord}:\Lambda\to\mathbb{Z}_{r^2}\times\mathbb{Z}_{r^2}$ (Witt vectors over $\mathbb{F}_{r^2}$) satisfying `IsOrderCoord`: additive, sending $1$ to $(1,0)$, multiplicative for the twisted rule involving $r$ and the Witt Frobenius, injective, with $r$-adically dense image, and compatible with reduced traces. Let $A_0$ be a fake elliptic curve over $k_0$ with $\Lambda$-action and level $N$ datum, $X_0$ a formal $\mathcal{O}_D$-module of dimension $2$ over $k_0$ (a commutative formal group with $\mathbb{Z}_{r^2}$-action and uniformiser endomorphism $\varpi$ satisfying $\varpi^2=[r]$ and $\varpi\circ[\alpha]=[\alpha^{\sigma}]\circ\varpi$), and $\theta_0$ formal coordinates of dimension $2$ for $A_0.f$ exhibiting $A_0$ as a formal module via $\mathrm{coord}$ and $X_0$ in the sense of `IsFormalModuleVia`. Let $\Gamma_t$ be a subgroup of $\mathbb{H}[\mathbb{Q},a_1,b_1]^\times$, $\iota_0$ a $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a_1,b_1]\to M_2(K_0)$, and $e:\Gamma_t\to\operatorname{End}(A_0.A)$ with each $e_\gamma$ over the base ($e_\gamma$ followed by $A_0.f$ is $A_0.f$) and commuting with the $\Lambda$-action ($[x]$ followed by $e_\gamma$ equals $e_\gamma$ followed by $[x]$), satisfying multiplicativity up to $r$-powers: for all $\gamma,\gamma'$ there are $i,j$ with $e_{\gamma\gamma'}$ followed by $[r^i]$ equal to $e_{\gamma'}$ followed by $e_\gamma$ followed by $[r^j]$. Let $P_0$ be a full level-$n$ structure on $A_0$, and assume there is a labelling $\mathrm{lab}:\Gamma_t\to\Lambda$ with $e_\gamma P_0=[\mathrm{lab}\,\gamma]P_0$, with $\mathrm{lab}(\gamma\gamma')-\mathrm{lab}(\gamma')\,\mathrm{lab}(\gamma)\in n\Lambda$, and with $\mathrm{lab}\,\gamma-c\in n\Lambda$ whenever $\gamma$ is the integer scalar $c$. Finally let $E$ be a ring homomorphism from the centraliser of $\{\text{all }[\alpha]\}\cup\{\varpi\}$ in $\operatorname{End}(X_0.F)$ to $M_2(K_0)$, let $g\in\mathrm{GL}_2(K_0)$, and let $\varepsilon_\gamma$ in that centraliser and $k_\gamma\in\mathbb{Z}$ be such that $\varepsilon_\gamma$ is the germ of $e_\gamma$ in the coordinates $\theta_0$ (on every nilpotent test point, $\theta_0$ of the truncated evaluation of $\varepsilon_\gamma$ agrees with $e_\gamma$ applied to $\theta_0$) and $E(\varepsilon_\gamma)=r^{k_\gamma}\,g\,\iota_0(\gamma)\,g^{-1}$. Then there is a group homomorphism $\kappa:\Gamma_t\to(\mathbb{Z}/n)^\times$ such that for every $\gamma$ one has $\kappa(\gamma)\cdot r^{(-k_\gamma)^{+}}=r^{(k_\gamma)^{+}}$ in $\mathbb{Z}/n$, where $(\cdot)^{+}$ denotes the truncation of an integer to a natural number; that is, $\kappa(\gamma)$ is the class of $r^{k_\gamma}$.
--
--   In the Čerednik–Drinfeld comparison, the dictionary relating endomorphisms of a fake elliptic curve to quaternionic group elements is determined only up to a power of the uniformising prime $r$; this statement records that the resulting exponents $k_\gamma$ assemble, modulo $n$, into a character of $\Gamma_t$ with values in $(\mathbb{Z}/n)^\times$. It is used in the fine-moduli comparison step [`CerednikDrinfeld.QM.IsFineModuli.exists_levelHom_translate_fibre_of_fineFamily_of_isNoetherianRing_heightNormalised_conn_eq_oneLegC5`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_levelHom_translate_fibre_of_fineFamily_of_isNoetherianRing_heightNormalised_conn_eq_oneLegC5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm
    {r : ℕ} [Fact r.Prime] {a b a₁ b₁ : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {N : ℕ} (n : ℕ) [NeZero n] (hrn : ¬ r ∣ n)
    {k₀ : Type} [CommRing k₀] [Nontrivial k₀] {K₀ : Type} [Field K₀] [CharZero K₀]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N k₀) (X₀ : FormalODModule r k₀) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)
    (hecomm : ∀ (γ : ↥Γt) (x : ↥Λ), A₀.act x ≫ e γ = e γ ≫ A₀.act x)
    (hE1mul :
      (∀ γ γ' : ↥Γt, ∃ i j : ℕ,
          e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (P₀ : A₀.FullLevel n)
    (hlab : ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])))
    (E : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (ε : ↥Γt → ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k : ↥Γt → ℤ)
    (hεk : ∀ γ : ↥Γt,
      (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ),
          J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (((ε γ) : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
            mapPt (e γ) (he γ) (θ₀ B' s)) ∧
      E (ε γ) = ((r : K₀) ^ k γ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) :
    ∃ κ : ↥Γt →* (ZMod n)ˣ,
      ∀ γ : ↥Γt, ((κ γ : (ZMod n)ˣ) : ZMod n) * (r : ZMod n) ^ (-(k γ)).toNat = (r : ZMod n) ^ (k γ).toNat := by sorry
