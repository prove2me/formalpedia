-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
-- name    : CerednikDrinfeld.QM.forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ad67b2ea-78e0-5584-a2ac-952b3e9009a6
-- title:
--   Mod N commutant of j(Λ) is blk(τ R)
-- statement:
--   Fix primes $r,\bar r$ with $\bar r\neq r$ and a nonzero $N$ with $r\nmid N$, $\bar r\nmid N$ and $N$ squarefree. Let $a,b\in\mathbb Q$ be such that $\mathbb H[\mathbb Q,a,b]$ satisfies $0<a$ or $0<b$ and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $v$ contains $r$ or $\bar r$; let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order (contains $1$, is closed under multiplication, spans the algebra over $\mathbb Q$, finitely generated) and is maximal among orders. Let $c,d<0$ with $\mathbb H[\mathbb Q,c,d]$ a division algebra at exactly the primes above $r$, and $O\subseteq\mathbb H[\mathbb Q,c,d]$ an order, maximal among orders. Let $\mu:O\to M_2(\mathbb Z/N)$ be additive, send $1$ to $1$, be multiplicative on products, be surjective, and satisfy $\mu(x)=0$ iff $x\in N\cdot O$. Let $j:\mathbb H[\mathbb Q,a,b]\to M_2(\mathbb H[\mathbb Q,c,d])$ be a $\mathbb Q$-algebra map with all entries of $j(m)$ in $O$ for $m\in\Lambda$; let $a_1,b_1<0$ with $\mathbb H[\mathbb Q,a_1,b_1]$ a division algebra at exactly the primes above $\bar r$, and $\tau:\mathbb H[\mathbb Q,a_1,b_1]\to M_2(\mathbb H[\mathbb Q,c,d])$ an injective $\mathbb Q$-algebra map whose image is exactly the centraliser of $j(\mathbb H[\mathbb Q,a,b])$; let $R$ be a $\mathbb Z$-submodule with $x\in R$ iff all entries of $\tau x$ lie in $O$. Writing $V=(\mathbb Z/N)^{2\times 2}$ and $\mathrm{blk}(y)w=\bigl(\sum_l\mu(y_{il})\,w_l\bigr)_i$ for matrices $y$ with entries in $O$, the conclusion is threefold: (i) $\mathrm{blk}(\tau x)$ and $\mathrm{blk}(j m)$ commute on $V$ for all $x\in R$, $m\in\Lambda$; (ii) every $\mathbb Z/N$-linear endomorphism $\beta$ of $V$ commuting with all $\mathrm{blk}(j m)$, $m\in\Lambda$, equals $\mathrm{blk}(\tau x)$ for some $x\in R$; (iii) for $x\in R$, $\mathrm{blk}(\tau x)=0$ iff $x=N\cdot y$ for some $y\in R$.
--
--   This is the purely algebraic core of the comparison of level structures in the Čerednik–Drinfel'd setting: it identifies the commutant, inside $\mathrm{End}_{\mathbb Z/N}(V)$, of the mod-$N$ action of a maximal order $\Lambda$ in the indefinite quaternion algebra with the reduction of the centraliser order $R$ in the definite algebra ramified at $\bar r$, together with the exact kernel $NR$. It feeds the construction of Eichler orders and level structures on fake elliptic curves, where the ring laws for $\mu$ are supplied from the action on the $N$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.QM.forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (hH' : IsDefiniteRamifiedExactlyAt c d r) (hOmax : IsMaximalOrder O)

    (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
    (hμ_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, μ ⟨1, h⟩ = 1)
    (hμ_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O), μ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = μ x * μ y)
    (hμ_add : ∀ x y : ↥O, μ (x + y) = μ x + μ y)
    (hμ_surj : Function.Surjective μ)
    (hμ_ker : ∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d]))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :

    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R) (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N),
        (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) ((fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) l)) =
          (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) ((fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) l))) ∧

    (∀ β : (Fin 2 → Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → Fin 2 → ZMod N),
        (∀ (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N),
            β (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) = (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) ((β w) l))) →
        ∃ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R), ∀ w : Fin 2 → Fin 2 → ZMod N, β w = (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l))) ∧

    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R),
        (∀ w : Fin 2 → Fin 2 → ZMod N, (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) = 0) ↔
          ∃ y ∈ R, x = (N : ℚ) • y) := by sorry
